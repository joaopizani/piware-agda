\begin{code}
open import PiWare.Atom
open import PiWare.Gates

module PiWare.Simulation.Core {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_; _$_; const)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz)
open import Data.Product using (_×_; _,_; proj₁; uncurry′) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Stream using (Stream; _∷_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.CausalStream using (Γᶜ; _⇒ᶜ_; tails⁺)
open import PiWare.Utils using (unzip⁺; splitAt'; splitAt⁺; uncurry⁺)
open import Data.Vec using (Vec; _++_; lookup; replicate; allFin; drop)
                     renaming ([] to ε; _∷_ to _◁_; take to takeᵥ; map to mapᵥ)

open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

open import PiWare.Synthesizable At using (W; untag; untagList)
open import PiWare.Circuit.Core Gt
    using (ℂ'; Anyℂ'; Comb; Nil; Gate; Plug; DelayLoop; _|'_; _|+'_; _⟫'_; _Named_)
open Atomic At using (Atom#; n→atom)
open Gates At Gt using (spec)
\end{code}


-- helpers for circuit evaluation (both combinational and sequential)
%<*plugOutputs>
\begin{code}
plugOutputs : {α : Set} {o i : ℕ} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = mapᵥ (λ fin → lookup (p fin) ins) (allFin _)
\end{code}
%</plugOutputs>


-- combinational eval
%<*eval-core>
\begin{code}
⟦_⟧' : {i o : ℕ} → (c : ℂ' {Comb} i o) → (W i → W o)
⟦ Nil ⟧' = const ε
⟦ Gate g#  ⟧' = spec g#
⟦ Plug p   ⟧' = plugOutputs p
⟦ c Named _ ⟧' = ⟦ c ⟧'
⟦ c₁ ⟫' c₂ ⟧' = ⟦ c₂ ⟧' ∘ ⟦ c₁ ⟧'
⟦ _|'_  {i₁} c₁ c₂ ⟧' = uncurry′ _++_ ∘ mapₚ ⟦ c₁ ⟧' ⟦ c₂ ⟧' ∘ splitAt' i₁
⟦ _|+'_ {i₁} c₁ c₂ ⟧' = [ ⟦ c₁ ⟧' , ⟦ c₂ ⟧' ]′ ∘ untag {i₁}
\end{code}
%</eval-core>


-- sequential eval as "causal stream function"
-- again the "uncurrying trick" to convince the termination checker
%<*delay>
\begin{code}
delay : ∀ {i o l} (c : ℂ' {Comb} (i + l) (o + l)) → W i ⇒ᶜ W (o + l)
delay {i} {o} {l} c = uncurry⁺ (delay' {i} {o} {l} c)
  where
    delay' : ∀ {i o l} (c : ℂ' {Comb} (i + l) (o + l)) → W i → List (W i) → W (o + l)
    delay' {_} {_} c w⁰ [] = ⟦ c ⟧' (w⁰ ++ replicate (n→atom Fz))
    delay' {_} {o} c w⁰ (w⁻¹ ∷ w⁻) = ⟦ c ⟧' (w⁰ ++ drop o (delay' {_} {o} c w⁻¹ w⁻))
\end{code}
%</delay>

%<*eval-causal>
\begin{code}
⟦_⟧ᶜ : {i o : ℕ} → ℂ' i o → (W i ⇒ᶜ W o)
⟦ Nil     ⟧ᶜ (w⁰ ∷ _) = ⟦ Nil ⟧' w⁰
⟦ Gate g# ⟧ᶜ (w⁰ ∷ _) = ⟦ Gate g# ⟧' w⁰
⟦ Plug p  ⟧ᶜ (w⁰ ∷ _) = plugOutputs p w⁰
⟦ c Named _ ⟧ᶜ = ⟦ c ⟧ᶜ
⟦ DelayLoop {o = j} c ⟧ᶜ = takeᵥ j ∘ delay {o = j} c
⟦ c₁ ⟫' c₂ ⟧ᶜ = ⟦ c₂ ⟧ᶜ ∘ map⁺ ⟦ c₁ ⟧ᶜ ∘ tails⁺
⟦ _|'_ {i₁} c₁ c₂ ⟧ᶜ = uncurry′ _++_ ∘ mapₚ ⟦ c₁ ⟧ᶜ ⟦ c₂ ⟧ᶜ ∘ unzip⁺ ∘ splitAt⁺ i₁
⟦ _|+'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ ∷ w⁻) with untag {i₁} w⁰ | untagList {i₁} w⁻
... | inj₁ w⁰₁ | w⁻₁ , _   = ⟦ c₁ ⟧ᶜ (w⁰₁ ∷ w⁻₁)
... | inj₂ w⁰₂ | _   , w⁻₂ = ⟦ c₂ ⟧ᶜ (w⁰₂ ∷ w⁻₂)
\end{code}
%</eval-causal>

%<*run-causal>
\begin{code}
runᶜ : ∀ {α β} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ∷ x⁺) = runᶜ' f ((x⁰ ∷ []) , ♭ x⁺)
    where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
          runᶜ' f ((x⁰ ∷ x⁻) , (x¹ ∷ x⁺)) = f (x⁰ ∷ x⁻) ∷ ♯ runᶜ' f ((x¹ ∷ x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}
%</run-causal>

%<*eval-seq-core>
\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ' i o → (Stream (W i) → Stream (W o))
⟦_⟧*' = runᶜ ∘ ⟦_⟧ᶜ
\end{code}
%</eval-seq-core>
