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
open import Data.CausalStream using (Γᶜ; _⇒ᶜ_; tails⁺)
open import PiWare.Utils using (unzip⁺; splitAt'; splitAt⁺)
open import Data.Vec using (Vec; _++_; splitAt; lookup; replicate; allFin)
                     renaming ([] to ε; _∷_ to _◁_; take to takeᵥ; map to mapᵥ)

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
⟦_⟧' : {i o : ℕ} → (c : ℂ' i o) {p : comb' c} → (𝕎 i → 𝕎 o)
⟦ Nil ⟧' = const ε
⟦ Gate g#  ⟧' = spec g#
⟦ Plug p   ⟧' = plugOutputs p
⟦ c₁ ⟫' c₂ ⟧' {p₁ , p₂} = ⟦ c₂ ⟧' {p₂} ∘ ⟦ c₁ ⟧' {p₁}
⟦ _|'_  {i₁} c₁ c₂ ⟧' {p₁ , p₂} = uncurry′ _++_ ∘ mapₚ (⟦ c₁ ⟧' {p₁}) (⟦ c₂ ⟧' {p₂}) ∘ splitAt' i₁
⟦ _|+'_ {i₁} c₁ c₂ ⟧' {p₁ , p₂} = [ ⟦ c₁ ⟧' {p₁} , ⟦ c₂ ⟧' {p₂} ]′ ∘ untag {i₁}
⟦ DelayLoop c ⟧' {()} v
\end{code}
%</eval-core>


-- sequential eval as "causal stream function"
-- again the "uncurrying trick" to convince the termination checker
%<*delay>
\begin{code}
delay : ∀ {i o l} (c : ℂ' (i + l) (o + l)) {p : comb' c} → 𝕎 i ⇒ᶜ 𝕎 (o + l)
delay {i} {o} {l} c {p} = uncurry′ (delay' {i} {o} {l} c {p})
  where
    delay' : ∀ {i o l} (c : ℂ' (i + l) (o + l)) {p : comb' c} → W i → List (W i) → W (o + l)
    delay' {_} {_} c {p} w⁰ [] = ⟦ c ⟧' {p} (w⁰ ++ replicate (n→atom Fz))
    delay' {_} {o} c {p} w⁰ (w⁻¹ ∷ w⁻) with splitAt o (delay' {_} {o} c {p} w⁻¹ w⁻)
    delay' {_} {o} c {p} w⁰ (w⁻¹ ∷ w⁻) | _ , b⁻¹ , _ = ⟦ c ⟧' {p} (w⁰ ++ b⁻¹)
\end{code}
%</delay>
-- HERE, (⟦ c ⟧' {p} (w⁰ ++ b⁻¹)), in the time difference between w⁰ and b⁻¹, resides the delay!

%<*eval-causal>
\begin{code}
⟦_⟧ᶜ : {i o : ℕ} → ℂ' i o → (𝕎 i ⇒ᶜ 𝕎 o)
⟦ Nil     ⟧ᶜ (w⁰ , _) = ⟦ Nil ⟧' w⁰
⟦ Gate g# ⟧ᶜ (w⁰ , _) = ⟦ Gate g# ⟧' w⁰
⟦ Plug p  ⟧ᶜ (w⁰ , _) = plugOutputs p w⁰
⟦ DelayLoop {o = j} c ⟧ᶜ = takeᵥ j ∘ delay {o = j} c
⟦ c₁ ⟫' c₂ ⟧ᶜ = ⟦ c₂ ⟧ᶜ ∘ map⁺ ⟦ c₁ ⟧ᶜ ∘ tails⁺
⟦ _|'_ {i₁} c₁ c₂ ⟧ᶜ = uncurry′ _++_ ∘ mapₚ ⟦ c₁ ⟧ᶜ ⟦ c₂ ⟧ᶜ ∘ unzip⁺ ∘ splitAt⁺ i₁
⟦ _|+'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ , w⁻) with untag {i₁} w⁰ | untagList {i₁} w⁻
... | inj₁ w⁰₁ | w⁻₁ , _   = ⟦ c₁ ⟧ᶜ (w⁰₁ , w⁻₁)
... | inj₂ w⁰₂ | _   , w⁻₂ = ⟦ c₂ ⟧ᶜ (w⁰₂ , w⁻₂)
\end{code}
%</eval-causal>

%<*run-causal>
\begin{code}
runᶜ : ∀ {α β} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ∷ x⁺) = runᶜ' f ((x⁰ , []) , ♭ x⁺)
    where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
          runᶜ' f ((x⁰ , x⁻) , (x¹ ∷ x⁺)) = f (x⁰ , x⁻) ∷ ♯ runᶜ' f ((x¹ , x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}
%</run-causal>

%<*eval-seq-core>
\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ' i o → (Stream (𝕎 i) → Stream (𝕎 o))
⟦_⟧*' = runᶜ ∘ ⟦_⟧ᶜ
\end{code}
%</eval-seq-core>
