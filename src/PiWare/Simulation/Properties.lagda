\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_; flip)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using (lookup; tabulate)

open import Data.Nat.Properties.Simple using () renaming (+-right-identity to +-identityᵣ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Data.Vec.Properties using (tabulate-allFin; map-lookup-allFin; lookup∘tabulate)
open import Data.Vec.Extra using (splitAt-i+0)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open module VecPropsEq {a} {α : Set a} = Data.Vec.Properties.UsingVectorEquality (setoid α) using (xs++[]=xs)
open VecPropEq using (from-≡; to-≡) renaming (refl to reflᵥ)

open Atomic At using (W)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Circuit Gt using (ℂ; Nil; Plug; _⟫_; _∥_)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWare.Simulation.Equality Gt
  using (_≊_; _≋_; refl≋; begin_; _∎; _≈ℂ⟨_⟩_; ≡×≡⇒×≡×; ≊⇒≋; ≋-trans)
\end{code}


\begin{code}
-- Basic
id⤨-id : ∀ {i} (w : W i) → ⟦ id⤨ ⟧ w ≡ id w
id⤨-id w rewrite tabulate-allFin (λ i → lookup i w) = map-lookup-allFin w

private
  tabulate-ext : ∀ {a n} {A : Set a} {f g : Fin n → A} → (∀ x → f x ≡ g x) → tabulate f ≡ tabulate g
  tabulate-ext {n = zero}  _        = refl
  tabulate-ext {n = suc m} ∀x→fx≡gx rewrite ∀x→fx≡gx Fz | tabulate-ext (∀x→fx≡gx ∘ Fs) = refl

plug-∘ : ∀ {i m o} (f : Fin m → Fin i) (g : Fin o → Fin m) → Plug f ⟫ Plug g ≋ Plug (f ∘ g)
plug-∘ f g = ≊⇒≋ $ from-≡ ∘ λ w → tabulate-ext (λ x → lookup∘tabulate (λ y → lookup (f y) w) (g x))

plug-ext : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≋ Plug g
plug-ext f≡g = ≊⇒≋ $ from-≡ ∘ λ w → tabulate-ext (cong (flip lookup w) ∘ f≡g)

plugs⁻¹ : ∀ {i o} {f : Fin o → Fin i} {g : Fin i → Fin o} → (∀ x → f (g x) ≡ x) → Plug f ⟫ Plug g ≋ id⤨ {i}
plugs⁻¹ {f = f} {g} f∘g≡id = ≋-trans (plug-∘ f g) (plug-ext f∘g≡id)


-- Sequence monoid
⟫-identityᵣ : ∀ {i o} (c : ℂ i o) → c ⟫ id⤨ ≋ c
⟫-identityᵣ c = ≊⇒≋ (from-≡ ∘ id⤨-id ∘ ⟦ c ⟧)

⟫-identityₗ : ∀ {i o} (c : ℂ i o) → id⤨ ⟫ c ≋ c
⟫-identityₗ c = ≊⇒≋ (from-≡ ∘ cong ⟦ c ⟧ ∘ id⤨-id)

⟫-assoc : ∀ {i m n o} (c₁ : ℂ i m) (c₂ : ℂ m n) (c₃ : ℂ n o) → (c₁ ⟫ c₂) ⟫ c₃ ≋ c₁ ⟫ (c₂ ⟫ c₃)
⟫-assoc c₁ c₂ c₃ = ≊⇒≋ (from-≡ ∘ λ _ → refl)


-- Parallel monoid
∥-identityₗ : ∀ {i o} (c : ℂ i o) → Nil {0} ∥ c ≋ c
∥-identityₗ _ = ≊⇒≋ (λ _ → reflᵥ _)

∥-identityᵣ : ∀ {i o} (c : ℂ i o) → c ∥ Nil {0} ≋ c
∥-identityᵣ {i} {o} c = refl≋ (+-identityᵣ i) ∥-identityᵣ-≊
  where ∥-identityᵣ-≊ : c ∥ Nil {0} ≊ c
        ∥-identityᵣ-≊ w≈w′ rewrite to-≡ (splitAt-i+0 w≈w′) = xs++[]=xs (⟦ c ⟧ _)

∥-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} {c₃ : ℂ i₃ o₃} → (c₁ ∥ c₂) ∥ c₃ ≋ c₁ ∥ (c₂ ∥ c₃)
∥-assoc = {!!}
\end{code}
