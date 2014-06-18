\begin{code}
module PiWare.Simulation.Core where

open import Function using (_∘_; _$_; id)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)

open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; <_,_>; proj₁) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Stream using (Stream; _∷_; zipWith) renaming (map to mapₛ)
open import Data.Vec using (Vec; _++_; splitAt; lookup; replicate; allFin)
                     renaming (_∷_ to _◁_; take to takeᵥ; map to mapᵥ; [_] to [_]ᵥ)

open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty using () renaming (map to map⁺)
open import Data.CausalStream using (Γᶜ; _⇒ᶜ_; tails⁺)
open import PiWare.Utils using (unzip)

-- TODO: Now hardcoded to Atom𝔹, generalize later (module parameter AtomInfo)
open import PiWare.Circuit.Core
open import PiWare.Atom
open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Synthesizable Atom𝔹 using (𝕎; splitListByTag; tagToSum)
open AtomInfo Atom𝔹
\end{code}


-- helpers for circuit evaluation (both combinational and sequential)
%<*plugOutputs>
\begin{code}
plugOutputs : {α : Set} {o i : ℕ} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = mapᵥ (λ fin → lookup (p fin) ins) (allFin _)
\end{code}
%</plugOutputs>

\begin{code}
splitVecs : {α : Set} (n : ℕ) {m : ℕ} → List (Vec α (n + m)) → List (Vec α n) × List (Vec α m)
splitVecs n = unzip ∘ map (mapₚ id proj₁ ∘ splitAt n)
\end{code}


-- combinational eval
%<*eval'>
\begin{code}
⟦_⟧' : {i o : ℕ} → (c : ℂ' Atom𝔹 i o) {p : comb' c} → (𝕎 i → 𝕎 o)
⟦ Not ⟧' (x ◁ ε)     = [ not x ]ᵥ
⟦ And ⟧' (x ◁ y ◁ ε) = [ x ∧ y ]ᵥ
⟦ Or  ⟧' (x ◁ y ◁ ε) = [ x ∨ y ]ᵥ
⟦ Plug p   ⟧' w = plugOutputs p w
⟦ c₁ ⟫' c₂ ⟧' {p = (p₁ , p₂)} = ⟦ c₂ ⟧' {p = p₂} ∘ ⟦ c₁ ⟧' {p = p₁}
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} w with splitAt i₁ w
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} .(w₁ ++ w₂) | w₁ , w₂ , refl = ⟦ c₁ ⟧' {p = p₁} w₁ ++ ⟦ c₂ ⟧' {p = p₂} w₂
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} w with tagToSum {i₁} w
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} w | inj₁ w₁ = ⟦ c₁ ⟧' {p = p₁} w₁
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} w | inj₂ w₂ = ⟦ c₂ ⟧' {p = p₂} w₂
⟦ DelayLoop c ⟧' {()} v
\end{code}
%</eval'>


-- sequential eval as "causal stream function"
\begin{code}
delay : {i o l : ℕ} (c : ℂ' Atom𝔹 (i + l) (o + l)) {p : comb' c} → 𝕎 i → List (𝕎 i) → 𝕎 (o + l)
delay {_} {_} c {p} w⁰ []                       = ⟦ c ⟧' {p} (w⁰ ++ replicate false)
delay {_} {o} c {p} w⁰ (w⁻¹ ∷ w⁻) with splitAt o (delay {_} {o} c {p} w⁻¹ w⁻)
delay {_} {o} c {p} w⁰ (w⁻¹ ∷ w⁻) | _ , b⁻¹ , _ = ⟦ c ⟧' {p} (w⁰ ++ b⁻¹)
-- HERE, (⟦ c ⟧' {p} (v⁰ ++ b⁻¹)), in the time difference between i⁰ and l⁻¹, resides the delay!
\end{code}

\begin{code}
⟦_⟧ᶜ : {i o : ℕ} → ℂ' Atom𝔹 i o → (𝕎 i ⇒ᶜ 𝕎 o)
⟦ Not         ⟧ᶜ (w⁰ , _) = ⟦ Not ⟧' w⁰
⟦ And         ⟧ᶜ (w⁰ , _) = ⟦ And ⟧' w⁰
⟦ Or          ⟧ᶜ (w⁰ , _) = ⟦ Or  ⟧' w⁰
⟦ Plug p      ⟧ᶜ (w⁰ , _) = plugOutputs p w⁰
⟦ DelayLoop {o = o} c {p} ⟧ᶜ (w⁰ , w⁻) = takeᵥ o (delay {o = o} c {p} w⁰ w⁻)
⟦ c₁ ⟫' c₂ ⟧ᶜ ws = ⟦ c₂ ⟧ᶜ (map⁺ ⟦ c₁ ⟧ᶜ (tails⁺ ws))
⟦ _|'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ , w⁻) with splitAt i₁ w⁰ | splitVecs i₁ w⁻
⟦ _|'_ {i₁} c₁ c₂ ⟧ᶜ (.(w⁰₁ ++ w⁰₂) , w⁻) | w⁰₁ , w⁰₂ , refl | w⁻₁ , w⁻₂ = ⟦ c₁ ⟧ᶜ (w⁰₁ , w⁻₁) ++ ⟦ c₂ ⟧ᶜ (w⁰₂ , w⁻₂)
⟦ _|+'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ , w⁻) with splitListByTag {i₁} w⁻ | tagToSum {i₁} w⁰
⟦ _|+'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ , w⁻) | w⁻₁ , _   | inj₁ w⁰₁ = ⟦ c₁ ⟧ᶜ (w⁰₁ , w⁻₁)
⟦ _|+'_ {i₁} c₁ c₂ ⟧ᶜ (w⁰ , w⁻) | _   , w⁻₂ | inj₂ w⁰₂ = ⟦ c₂ ⟧ᶜ (w⁰₂ , w⁻₂)
\end{code}

\begin{code}
runᶜ : ∀ {α β} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ∷ x⁺) = runᶜ' f ((x⁰ , []) , ♭ x⁺)
    where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
          runᶜ' f ((x⁰ , x⁻) , (x¹ ∷ x⁺)) = f (x⁰ , x⁻) ∷ ♯ runᶜ' f ((x¹ , x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}

\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ' Atom𝔹 i o → (Stream (𝕎 i) → Stream (𝕎 o))
⟦ c ⟧*' = runᶜ (⟦ c ⟧ᶜ)
\end{code}
