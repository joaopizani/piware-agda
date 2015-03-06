\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Simulation {At : Atomic} (Gt : Gates At) where

open import Function using (_∘′_; _$_; const; flip)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin) renaming (zero to Fz)
open import Data.Product using (_×_; _,_; proj₁; uncurry′) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Stream using (Stream; _∷_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.CausalStream using (Γᶜ; _⇒ᶜ_; tails⁺)
open import Data.Vec.Extra using (splitAt')
open import Data.List.NonEmpty.Extra using (unzip⁺; splitAt⁺; uncurry⁺)
open import Data.Vec using (Vec; _++_; lookup; replicate; allFin; drop)
                     renaming ([] to ε; _∷_ to _◁_; take to takeᵥ; map to mapᵥ)

open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

open import PiWare.Synthesizable At using (untag; untagList)
open import PiWare.Circuit Gt using (ℂ; σ; Nil; Gate; Plug; DelayLoop; _∥_; _|+_; _⟫_)
open Atomic At using (Atom#; n→atom; W)
open Gates At Gt using (spec; |in|; |out|)
\end{code}


-- helpers for circuit evaluation (both combinational and sequential)
%<*plugOutputs>
\AgdaTarget{plugOutputs}
\begin{code}
plugOutputs : ∀ {α : Set} {o i} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = mapᵥ (λ fin → lookup (p fin) ins) (allFin _)
\end{code}
%</plugOutputs>


%<*algebra-type>
\begin{code}
record ℂσ★ (Cₓ : ℕ → ℕ → Set) : Set where
  inductive
  field
    Nil★  : ∀ {n} → Cₓ n zero
    Gate★ : ∀ g# → Cₓ (|in| g#) (|out| g#)
    Plug★ : ∀ {i o} (f : Fin o → Fin i) → Cₓ i o

    _⟫★_  : ∀ {i m o}       → Cₓ i m   → Cₓ m o   → Cₓ i o
    _∥★_  : ∀ {i₁ o₁ i₂ o₂} → Cₓ i₁ o₁ → Cₓ i₂ o₂ → Cₓ (i₁ + i₂) (o₁ + o₂)
    _|+★_ : ∀ {i₁ i₂ o}     → Cₓ i₁ o  → Cₓ i₂ o  → Cₓ (suc (i₁ ⊔ i₂)) o
\end{code}
%</algebra-type>

%<*fold>
\begin{code}
module _ {Carrier : ℕ → ℕ → Set} (algebra : ℂσ★ Carrier) where
  open ℂσ★ algebra
  cataℂσ★ : ∀ {i o} → ℂ {σ} i o → Carrier i o
  cataℂσ★ Nil        = Nil★
  cataℂσ★ (Gate g#)  = Gate★ g#
  cataℂσ★ (Plug f)   = Plug★ f
  cataℂσ★ (c₁ ⟫ c₂)  = cataℂσ★ c₁ ⟫★ cataℂσ★ c₂
  cataℂσ★ (c₁ ∥ c₂)  = cataℂσ★ c₁ ∥★ cataℂσ★ c₂
  cataℂσ★ (c₁ |+ c₂) = cataℂσ★ c₁ |+★ cataℂσ★ c₂
\end{code}
%</fold>

%<*Word-function-type>
\begin{code}
W⟶W : ∀ m n → Set
W⟶W m n = W m → W n
\end{code}
%</Word-function-type>

%<*simulation-combinational-algebra>
\begin{code}
simulation-combinational★ : ℂσ★ (W⟶W)
simulation-combinational★ = record
  { Nil★  = const ε
  ; Gate★ = spec
  ; Plug★ = plugOutputs
  ; _⟫★_  = flip _∘′_
  ; _∥★_  = λ {i₁} f₁ f₂ → uncurry′ _++_ ∘′ mapₚ f₁ f₂ ∘′ splitAt' i₁
  ; _|+★_ = λ {i₁} f₁ f₂ → [ f₁ , f₂ ]′ ∘′ untag {i₁}
  }
\end{code}
%</simulation-combinational-algebra>

%<*eval>
\AgdaTarget{⟦\_⟧}
\begin{code}
⟦_⟧ : ∀ {i o} → ℂ {σ} i o → (W i → W o)
⟦_⟧ = cataℂσ★ simulation-combinational★
\end{code}
%</eval>


-- Sequential eval as "causal stream function". "uncurrying" to convince the termination checker
-- TODO: Now it's hardcoded to pad the sequence with th first element being (replicate (n→atom Fz))
%<*delay>
\AgdaTarget{delay}
\begin{code}
delay : ∀ {i o l} → ℂ {σ} (i + l) (o + l) → (W i ⇒ᶜ W (o + l))
delay {i} {o} {l} = uncurry⁺ ∘′ delay' {i} {o} {l}
  where delay' : ∀ {i o l} → ℂ {σ} (i + l) (o + l) → W i → List (W i) → W (o + l)
        delay' {_} {_} c w⁰ []         = ⟦ c ⟧ (w⁰ ++ replicate (n→atom Fz))
        delay' {_} {o} c w⁰ (w⁻¹ ∷ w⁻) = ⟦ c ⟧ (w⁰ ++ drop o (delay' {_} {o} c w⁻¹ w⁻))
\end{code}
%</delay>

%<*eval-causal>
\AgdaTarget{⟦\_⟧ᶜ}
\begin{code}
⟦_⟧ᶜ : ∀ {i o} → ℂ i o → (W i ⇒ᶜ W o)
⟦ Nil                 ⟧ᶜ (w⁰ ∷ _) = ⟦ Nil ⟧ w⁰
⟦ Gate g#             ⟧ᶜ (w⁰ ∷ _) = ⟦ Gate g# ⟧ w⁰
⟦ Plug p              ⟧ᶜ (w⁰ ∷ _) = plugOutputs p w⁰
⟦ DelayLoop {o = j} c ⟧ᶜ          = takeᵥ j ∘′ delay {o = j} c
⟦ c₁ ⟫ c₂         ⟧ᶜ = ⟦ c₂ ⟧ᶜ ∘′ map⁺ ⟦ c₁ ⟧ᶜ ∘′ tails⁺
⟦ _∥_ {i₁} c₁ c₂  ⟧ᶜ = uncurry′ _++_ ∘′ mapₚ ⟦ c₁ ⟧ᶜ ⟦ c₂ ⟧ᶜ ∘′ unzip⁺ ∘′ splitAt⁺ i₁

⟦ _|+_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ ∷ w⁻) with untag {i₁} w⁰ | untagList {i₁} w⁻
... | inj₁ w⁰₁ | w⁻₁ , _   = ⟦ c₁ ⟧ᶜ (w⁰₁ ∷ w⁻₁)
... | inj₂ w⁰₂ | _   , w⁻₂ = ⟦ c₂ ⟧ᶜ (w⁰₂ ∷ w⁻₂)
\end{code}
%</eval-causal>

%<*run-causal>
\AgdaTarget{runᶜ}
\begin{code}
runᶜ : ∀ {α β} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ∷ x⁺) = runᶜ' f ((x⁰ ∷ []) , ♭ x⁺)
    where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
          runᶜ' f ((x⁰ ∷ x⁻) , (x¹ ∷ x⁺)) = f (x⁰ ∷ x⁻) ∷ ♯ runᶜ' f ((x¹ ∷ x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}
%</run-causal>

%<*eval-seq>
\AgdaTarget{⟦\_⟧*'}
\begin{code}
⟦_⟧* : ∀ {i o} → ℂ i o → (Stream (W i) → Stream (W o))
⟦_⟧* = runᶜ ∘′ ⟦_⟧ᶜ
\end{code}
%</eval-seq>
