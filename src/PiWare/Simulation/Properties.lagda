\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_; flip)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (lookup; tabulate; splitAt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; setoid)
open import Data.Nat.Properties.Simple using () renaming (+-right-identity to +-identityᵣ)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commutativeSemiring)
open import Algebra using (module CommutativeSemiring; Monoid)
open CommutativeSemiring ℕ-commutativeSemiring using (+-assoc)

open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (from-≡; to-≡) renaming (refl to reflᵥ)
open import Data.Vec.Properties using (tabulate-allFin; map-lookup-allFin; lookup∘tabulate)
open module X {a} {α : Set a} = Data.Vec.Properties.UsingVectorEquality (setoid α) using (xs++[]=xs)
open import Data.Vec.Extra
  using (splitAt-i+0; ++-assoc; ++-assoc-split₁; ++-assoc-split₂; ++-assoc-split₃; splitAt-++; ₁; ₂′)

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
∥-assoc {i₁} {_} {i₂} {_} {i₃} {_} {c₁} {c₂} {c₃} = refl≋ (+-assoc i₁ i₂ i₃) ∥-assoc-≊  
  where ∥-assoc-≊ : (c₁ ∥ c₂) ∥ c₃ ≊ c₁ ∥ (c₂ ∥ c₃)
        ∥-assoc-≊ {w} {w′} w≈w′ rewrite to-≡ $ ++-assoc-split₁ {i₁} w≈w′
                                      | to-≡ $ ++-assoc-split₂ {i₁} w≈w′
                                      | sym (to-≡ $ ++-assoc-split₃ {i₁} w≈w′)
          = ++-assoc (⟦ c₁ ⟧ w₁) (⟦ c₂ ⟧ w₂) (⟦ c₃ ⟧ w₃)
          where w₁ = ₁ (splitAt i₁ w′)
                w₂ = (₁ ∘ splitAt i₂ ∘ ₂′) (splitAt i₁ w′)
                w₃ = ₂′ (splitAt (i₁ + i₂) w)


∥-id⤨ : ∀ {n m} → id⤨ {n} ∥ id⤨ {m} ≋ id⤨ {n + m}
∥-id⤨ {n} {m} = ≊⇒≋ (from-≡ ∘ f)
  where f : ∀ w → ⟦ id⤨ {n} ∥ id⤨ {m} ⟧ w ≡ ⟦ id⤨ {n + m} ⟧ w
        f w with splitAt n w
        f w | wₙ , wₘ , w≡wₙ⧺wₘ with id⤨-id wₙ | id⤨-id wₘ | id⤨-id w
        f w | wₙ , wₘ , w≡wₙ⧺wₘ | eq-wₙ | eq-wₘ | eq-w rewrite eq-wₙ | eq-wₘ | eq-w = sym w≡wₙ⧺wₘ


⟫-distrib-∥ : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ i₁ m₁) (f₂ : ℂ i₂ m₂) (g₁ : ℂ m₁ o₁) (g₂ : ℂ m₂ o₂) → (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂) ≋ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂)
⟫-distrib-∥ {i₁} {m₁} f₁ f₂ g₁ g₂ = ≊⇒≋ (from-≡ ∘ f)
  where f : ∀ w → ⟦ (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂) ⟧ w ≡ ⟦ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂) ⟧ w
        f w rewrite splitAt-++ m₁ (⟦ f₁ ⟧ $ ₁ (splitAt i₁ w)) (⟦ f₂ ⟧ $ ₂′ (splitAt i₁ w)) = refl
\end{code}



⟫-Monoid : ∀ i o → Monoid _ _
⟫-Monoid i o = record
  { Carrier = ℂ i o
  ; _≈_ = _≋_
  ; _∙_ = _⟫_
  ; isMonoid = record
      { isSemigroup = record
          { isEquivalence = ?
          ; assoc         = ?
          ; ∙-cong        = ?
          }
      ; identity    = ? , ?
      }
  }
