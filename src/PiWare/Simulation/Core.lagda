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
open import Data.List.NonEmpty using (List⁺) renaming (map to map⁺)
open import Data.CausalStream using (Γc; _⇒c_; tails⁺)
open import PiWare.Utils using (unzip⁺; splitAt'; splitAt⁺)
open import Data.Vec using (Vec; _++_; lookup; replicate; allFin; drop)
                     renaming ([] to ε; take to takeᵥ; map to mapᵥ)

open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

open import PiWare.Synthesizable At using (W; untag; untagList)
open import PiWare.Circuit.Core Gt using (ℂ'; comb'; Nil; Gate; Plug; DelayLoop; _|'_; _|+'_; _⟫'_)
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
⟦_⟧' : {i o : ℕ} → (c : ℂ' i o) {p : comb' c} → (W i → W o)
⟦ Nil      ⟧'  = const ε
⟦ Gate g#  ⟧'  = spec g#
⟦ Plug p   ⟧'  = plugOutputs p

⟦ DelayLoop c ⟧' {()} v

⟦ c₁ ⟫' c₂ ⟧' {p₁ , p₂} = ⟦ c₂ ⟧' {p₂} ∘ ⟦ c₁ ⟧' {p₁}

⟦ _|'_  {i₁} c₁ c₂ ⟧' {p₁ , p₂} =
    uncurry′ _++_ ∘ mapₚ (⟦ c₁ ⟧' {p₁}) (⟦ c₂ ⟧' {p₂}) ∘ splitAt' i₁

⟦ _|+'_ {i₁} c₁ c₂ ⟧' {p₁ , p₂} =
    [ ⟦ c₁ ⟧' {p₁} , ⟦ c₂ ⟧' {p₂} ]′ ∘ untag {i₁}
\end{code}
%</eval-core>


-- sequential eval as "causal stream function"
-- again the "uncurrying trick" to convince the termination checker
%<*delay>
\begin{code}
delay : ∀ {i o l} (c : ℂ' (i + l) (o + l)) {p : comb' c} → W i ⇒c W (o + l)
delay {i} {o} {l} c {p} = uncurry′ (delay' {i} {o} {l} c {p})
  where
    delay' : ∀ {i o l} (c : ℂ' (i + l) (o + l)) {p : comb' c} → W i → List (W i) → W (o + l)
    delay' {_} {_} c {p} w⁰ []          = ⟦ c ⟧' {p} (w⁰ ++ replicate (n→atom Fz))
    delay' {_} {o} c {p} w⁰ (w⁻¹ ∷ w⁻)  = ⟦ c ⟧' {p} (w⁰ ++ drop o (delay' {_} {o} c {p} w⁻¹ w⁻))
\end{code}
%</delay>
-- HERE, (⟦ c ⟧' {p} (w⁰ ++ b⁻¹)), in the time difference between w⁰ and b⁻¹, resides the delay!

%<*eval-causal>
\begin{code}
⟦_⟧c : {i o : ℕ} → ℂ' i o → (W i ⇒c W o)
⟦ Nil                      ⟧c  (w⁰ , _)  = ⟦ Nil ⟧' w⁰
⟦ Gate g#                  ⟧c  (w⁰ , _)  = ⟦ Gate g# ⟧' w⁰
⟦ Plug p                   ⟧c  (w⁰ , _)  = plugOutputs p w⁰
⟦ DelayLoop {o = j} c {p}  ⟧c            = takeᵥ j ∘ delay {o = j} c {p}

⟦ c₁ ⟫' c₂        ⟧c  = ⟦ c₂ ⟧c ∘ map⁺ ⟦ c₁ ⟧c ∘ tails⁺
⟦ _|'_ {i₁} c₁ c₂ ⟧c  = uncurry′ _++_ ∘ mapₚ ⟦ c₁ ⟧c ⟦ c₂ ⟧c ∘ unzip⁺ ∘ splitAt⁺ i₁

⟦ _|+'_ {i₁} c₁ c₂ ⟧c (w⁰ , w⁻) with untag {i₁} w⁰ | untagList {i₁} w⁻
... | inj₁ w⁰₁ | w⁻₁ , _    = ⟦ c₁ ⟧c (w⁰₁ , w⁻₁)
... | inj₂ w⁰₂ | _   , w⁻₂  = ⟦ c₂ ⟧c (w⁰₂ , w⁻₂)
\end{code}
%</eval-causal>

%<*run-causal>
\begin{code}
runc : ∀ {α β} → (α ⇒c β) → (Stream α → Stream β)
runc f (x⁰ ∷ x⁺) = runc' f ((x⁰ , []) , ♭ x⁺)
    where  runc' : ∀ {α β} → (α ⇒c β) → (Γc α × Stream α) → Stream β
           runc' f ((x⁰ , x⁻) , (x¹ ∷ x⁺)) =
               f (x⁰ , x⁻) ∷ ♯ runc' f ((x¹ , x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}
%</run-causal>

%<*eval-seq-core-decl>
\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ' i o → (Stream (W i) → Stream (W o))
\end{code}
%</eval-seq-core-decl>
%<*eval-seq-core-def>
\begin{code}
⟦_⟧*' = runc ∘ ⟦_⟧c
\end{code}
%</eval-seq-core-def>
