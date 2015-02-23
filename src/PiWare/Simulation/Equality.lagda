\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (_$_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; uncurry; _,_)
open import Level using () renaming (zero to lzero)

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Binary.Indexed using (Rel; IsEquivalence) renaming (Setoid to IndexedSetoid)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (_≈_; from-≡; to-≡)

open import PiWare.Circuit Gt using (ℂ; σ)
open import PiWare.Simulation Gt using (⟦_⟧)
open Atomic At using (W)
\end{code}


\begin{code}
ℂ₍₎ : (ℕ × ℕ) → Set
ℂ₍₎ = uncurry (ℂ {σ})

_≈⟦⟧_ : Rel ℂ₍₎ _
_≈⟦⟧_ {i₁ , o₁} {i₂ , o₂} c₁ c₂ = {w₁ : W i₁} {w₂ : W i₂} {p : w₁ ≈ w₂} → ⟦ c₁ ⟧ w₁ ≈ ⟦ c₂ ⟧ w₂

postulate isEquivalence₁ : IsEquivalence ℂ₍₎ _≈⟦⟧_

ℂ₍₎-setoid : IndexedSetoid (ℕ × ℕ) _ _
ℂ₍₎-setoid =
    record {
          Carrier       = ℂ₍₎
        ; _≈_           = _≈⟦⟧_
        ; isEquivalence = isEquivalence₁
    }
\end{code}

