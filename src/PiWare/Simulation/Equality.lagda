\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (_$_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; uncurry; _,_)
open import Level using () renaming (zero to lzero)

open import PiWare.Circuit Gt using (ℂ; σ)
open import PiWare.Simulation Gt using (⟦_⟧)
open Atomic At using (W; Atom)

open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using () renaming (refl to ≡-refl; cong to ≡-cong)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq {A = Atom} using (_≈_; from-≡; to-≡; refl; []-cong; _∷-cong_)
open import Relation.Binary.Indexed
    using (Rel; Reflexive; IsEquivalence) renaming (Setoid to ISetoid)

\end{code}


\begin{code}
ℂ₍₎ : (ℕ × ℕ) → Set
ℂ₍₎ = uncurry (ℂ {σ})

_≈⟦⟧_ : Rel ℂ₍₎ _
_≈⟦⟧_ {i₁ , o₁} {i₂ , o₂} c₁ c₂ = {w₁ : W i₁} {w₂ : W i₂} {p : w₁ ≈ w₂} → ⟦ c₁ ⟧ w₁ ≈ ⟦ c₂ ⟧ w₂

-- TODO: now it's specialized to Atom because of the way in which the VecPropEq module is open
coerce : ∀ {n₁ n₂} {v₁ : Vec Atom n₁} {v₂ : Vec Atom n₂} (p : v₁ ≈ v₂) → Vec Atom n₂
coerce {v₂ = []}       []-cong                = []
coerce {v₂ = x₂ ∷ xs₂} (x₁≈x₂ ∷-cong xs₁≈xs₂) = x₂ ∷ xs₂

≈-cong : ∀ {n₁ n₂} {v₁ : Vec Atom n₁} {v₂ : Vec Atom n₂} {f : Vec Atom n₂ → Vec Atom n₂} (p : v₁ ≈ v₂) → f (coerce p) ≈ f v₂
≈-cong {f = f} []-cong                = from-≡ (≡-cong f ≡-refl)
≈-cong {f = f} (x₁≈x₂ ∷-cong xs₁≈xs₂) = {!!}

≈⟦⟧-refl : Reflexive ℂ₍₎ _≈⟦⟧_
≈⟦⟧-refl = {!refl!} 

postulate isEquivalence₁ : IsEquivalence ℂ₍₎ _≈⟦⟧_

ℂ₍₎-setoid : ISetoid (ℕ × ℕ) _ _
ℂ₍₎-setoid =
    record {
          Carrier       = ℂ₍₎
        ; _≈_           = _≈⟦⟧_
        ; isEquivalence = isEquivalence₁
    }
\end{code}

