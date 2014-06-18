\begin{code}
module PiWare.Simulation.Core where

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Stream using (Stream; _∷_; zipWith) renaming (map to mapₛ)
open import Data.Vec using (Vec; _++_; splitAt; lookup; replicate; allFin)
                     renaming (_∷_ to _◁_; take to takeᵥ; map to mapᵥ; [_] to [_]ᵥ)

open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using () renaming (map to map⁺)
open import Data.CausalStream using (Γᶜ; _⇒ᶜ_; tails⁺)

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
splitVecₗ : {α : Set} (n m : ℕ) → List (Vec α (n + m)) → List (Vec α n) × List (Vec α m)
splitVecₗ _ _ [] = [] , []
splitVecₗ n m (v ∷ vs)           with splitAt n v | splitVecₗ n m vs
splitVecₗ n m (.(v₁ ++ v₂) ∷ vs) | v₁ , v₂ , refl | vs₁ , vs₂ = v₁ ∷ vs₁ , v₂ ∷ vs₂
\end{code}


-- combinational eval
%<*eval'>
\begin{code}
⟦_⟧' : {i o : ℕ} → (c : ℂ' Atom𝔹 i o) {p : comb' c} → (𝕎 i → 𝕎 o)
⟦ Not ⟧' (x ◁ ε)     = [ not x ]ᵥ
⟦ And ⟧' (x ◁ y ◁ ε) = [ x ∧ y ]ᵥ
⟦ Or  ⟧' (x ◁ y ◁ ε) = [ x ∨ y ]ᵥ
⟦ Plug p   ⟧' v = plugOutputs p v
⟦ c₁ ⟫' c₂  ⟧' {p = (p₁ , p₂)} v = ⟦ c₂ ⟧' {p = p₂} (⟦ c₁ ⟧' {p = p₁} v)
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} v with splitAt i₁ v
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} .(v₁ ++ v₂) | v₁ , v₂ , refl = ⟦ c₁ ⟧' {p = p₁} v₁ ++ ⟦ c₂ ⟧' {p = p₂} v₂
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} v with tagToSum {i₁} v
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} v | inj₁ v₁ = ⟦ c₁ ⟧' {p = p₁} v₁
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} v | inj₂ v₂ = ⟦ c₂ ⟧' {p = p₂} v₂
⟦ DelayLoop c ⟧' {()} v
\end{code}
%</eval'>


-- sequential eval as "causal stream function"

-- HERE, (⟦ c ⟧' {p} (i⁰ ++ l⁻¹)), in the time difference between i⁰ and l⁻¹, resides the delay!
\begin{code}
delay : {#i #o #l : ℕ} (c : ℂ' Atom𝔹 (#i + #l) (#o + #l)) {p : comb' c} → 𝕎 #i → List (𝕎 #i) → 𝕎 (#o + #l)
delay {_} {_ } c {p} i⁰ []                       = ⟦ c ⟧' {p} (i⁰ ++ replicate false)
delay {_} {#o} c {p} i⁰ (i⁻¹ ∷ i⁻) with splitAt #o (delay {_} {#o} c {p} i⁻¹ i⁻)
delay {_} {#o} c {p} i⁰ (i⁻¹ ∷ i⁻) | _ , l⁻¹ , _ = ⟦ c ⟧' {p} (i⁰ ++ l⁻¹)
\end{code}

\begin{code}
⟦_⟧ᶜ : {#i #o : ℕ} → ℂ' Atom𝔹 #i #o → (𝕎 #i ⇒ᶜ 𝕎 #o)
⟦ Not         ⟧ᶜ (i⁰ , _) = ⟦ Not ⟧' i⁰ 
⟦ And         ⟧ᶜ (i⁰ , _) = ⟦ And ⟧' i⁰
⟦ Or          ⟧ᶜ (i⁰ , _) = ⟦ Or  ⟧' i⁰
⟦ Plug p      ⟧ᶜ (i⁰ , _) = plugOutputs p i⁰
⟦ DelayLoop {o = #o} c {p} ⟧ᶜ (i⁰ , i⁻) = takeᵥ #o (delay {#o = #o} c {p} i⁰ i⁻)
⟦ c₁ ⟫' c₂ ⟧ᶜ is = ⟦ c₂ ⟧ᶜ (map⁺ ⟦ c₁ ⟧ᶜ (tails⁺ is))
⟦ _|'_ {#i₁} c₁ c₂ ⟧ᶜ (i⁰ , i⁻) with splitAt #i₁ i⁰ | splitVecₗ #i₁ _ i⁻
⟦ _|'_ {#i₁} c₁ c₂ ⟧ᶜ (.(i⁰₁ ++ i⁰₂) , i⁻) | i⁰₁ , i⁰₂ , refl | i⁻₁ , i⁻₂ = ⟦ c₁ ⟧ᶜ (i⁰₁ , i⁻₁) ++ ⟦ c₂ ⟧ᶜ (i⁰₂ , i⁻₂)
⟦ _|+'_ {#i₁} c₁ c₂ ⟧ᶜ (i⁰ , i⁻) with splitListByTag {#i₁} i⁻ | tagToSum {#i₁} i⁰
⟦ _|+'_ {#i₁} c₁ c₂ ⟧ᶜ (i⁰ , i⁻) | i⁻₁ , _   | inj₁ i⁰₁ = ⟦ c₁ ⟧ᶜ (i⁰₁ , i⁻₁)
⟦ _|+'_ {#i₁} c₁ c₂ ⟧ᶜ (i⁰ , i⁻) | _   , i⁻₂ | inj₂ i⁰₂ = ⟦ c₂ ⟧ᶜ (i⁰₂ , i⁻₂)
\end{code}

\begin{code}
runCST' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
runCST' f ((x⁰ , x⁻) , (x¹ ∷ x⁺)) = f (x⁰ , x⁻) ∷ ♯ runCST' f ((x¹ , x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}

\begin{code}
runCST : ∀ {α β} → (α ⇒ᶜ β) → (Stream α → Stream β)
runCST f (x⁰ ∷ x⁺) = runCST' f ((x⁰ , []) , ♭ x⁺)
\end{code}

\begin{code}
⟦_⟧*' : {#i #o : ℕ} → ℂ' Atom𝔹 #i #o → (Stream (𝕎 #i) → Stream (𝕎 #o))
⟦ c ⟧*' = runCST (⟦ c ⟧ᶜ)
\end{code}
