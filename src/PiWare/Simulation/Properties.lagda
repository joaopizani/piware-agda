\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_; _on_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using (lookup; tabulate)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (from-≡)
open import Data.Vec.Properties using (tabulate-allFin; map-lookup-allFin; lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Atomic At using (W)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Circuit Gt using (ℂ; Nil; Plug; _⟫_; _∥_)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWare.Simulation.Equality Gt
  using (_≋_; refl≋; begin_; _∎; _≈ℂ⟨_⟩_; ≣⇒≋; refl≣; ≣-trans; ≡×≡⇒×≡×)

import Algebra as A
import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (+-identity)
+-identity-right = proj₂ +-identity
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
plug-∘ f g = ≣⇒≋ $ refl≣ (λ w → {!!})
-- tabulate-ext (λ fin → lookup∘tabulate (λ fin₁ → lookup (f fin₁) w) (g fin))
{-
       (λ fin →
          lookup (g fin)
          (Data.Vec.replicate (λ fin₁ → lookup (f fin₁) w) Data.Vec.⊛
           tabulate (λ x → x)))
      ≡
         (λ fin → lookup (f (g fin)) w)
-}

plug-ext : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≋ Plug g
plug-ext p = ≣⇒≋ $ refl≣ (λ w → {!!})

plugs-inverse : ∀ {i o} {f : Fin o → Fin i} {g : Fin i → Fin o} → (∀ x → (f ∘ g) x ≡ id x) → Plug f ⟫ Plug g ≋ id⤨ {i}
plugs-inverse {f = f} {g = g} f∘g≡id = {!!}


-- Sequence monoid
⟫-identity-right : ∀ {i o} (c : ℂ i o) → c ⟫ id⤨ ≋ c
⟫-identity-right c = refl≋ refl (from-≡ ∘ id⤨-id ∘ ⟦ c ⟧)

⟫-identity-left : ∀ {i o} (c : ℂ i o) → id⤨ ⟫ c ≋ c
⟫-identity-left c = refl≋ refl (from-≡ ∘ cong ⟦ c ⟧ ∘ id⤨-id)

⟫-assoc : ∀ {i m n o} (c₁ : ℂ i m) (c₂ : ℂ m n) (c₃ : ℂ n o) → (c₁ ⟫ c₂) ⟫ c₃ ≋ c₁ ⟫ (c₂ ⟫ c₃)
⟫-assoc _ _ _ = refl≋ refl (λ _ → from-≡ refl)


-- Parallel monoid
∥-identity-left : ∀ {i o} (c : ℂ i o) → Nil {0} ∥ c ≋ c
∥-identity-left c = refl≋ refl (λ _ → from-≡ refl)

∥-identity-right : ∀ {i o} (c : ℂ i o) → c ∥ Nil {0} ≋ c
∥-identity-right {i} {o} c = refl≋ (≡×≡⇒×≡× (+-identity-right i , +-identity-right o)) {!!}
\end{code}
