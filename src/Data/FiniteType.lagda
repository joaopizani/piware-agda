\begin{code}
module Data.FiniteType where

open import Level using (_⊔_)

open import Function using (_⟨_⟩_; _$_)
open import Data.Nat.Base using (_+_; _*_; zero; suc; _≤″_; _<_) renaming (less-than-or-equal to lte≤″)
open import Data.Nat.Properties.Simple using (*-comm)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Nat.DivMod using (DivMod; module DivMod; _divMod_; _div_)
open import Data.Product using (_×_; _,_)

open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSR; module SemiringSolver to ℕ-SRSolver)
open ℕ-SRSolver using (solve; _:=_; con; _:+_; _:*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨⟩_; _≡⟨_⟩_)

open import Data.FiniteType.Base using (Finite; module Finite)

open DivMod using () renaming (remainder to ÷-rem; quotient to ÷-quot; property to ÷-prop)
\end{code}


\begin{code}
open Finite ⦃ … ⦄
\end{code}


\begin{code}
lemma₁ : ∀ a b c → a + b * (suc c) ≡ b + (a + c * b)
lemma₁ = solve 3 eq refl
  where eq = λ a b c → a :+ (b :* (con 1 :+ c)) := b :+ (a :+ c :* b)

divMod≤″ : ∀ {x y} (r : DivMod x (suc y)) → ÷-quot r ≤″ x
divMod≤″ {x} {y} r = lte≤″ eq
  where
    rem  = toℕ (÷-rem r)
    quot = ÷-quot r
    eq   = sym $ ÷-prop r  ⟨ trans ⟩  lemma₁ rem quot y

postulate lemma₂ : ∀ {n x} {i : Fin n} → x ≤″ (toℕ i) → x < n

splitFin× : ∀ {x y} → Fin (x * suc y) → Fin x × Fin (suc y)
splitFin× {x} {y} i = fromℕ≤ {÷-quot r} {x} undefined , ÷-rem r
  where r = (toℕ i) divMod (suc y)
        postulate undefined : (toℕ i) div (suc y) < x  -- TODO

Finite-× : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} ⦃ fα : Finite {ℓ₁} α ⦄ ⦃ fβ : Finite {ℓ₂} β ⦄ → Finite {ℓ₁ ⊔ ℓ₂} (α × β)
Finite-× ⦃ fα ⦄ ⦃ fβ ⦄ = record { |α| = |α|′ * |β|′
                                ; surjection = record { to = {!!}
                                                      ; surjective = record { from = {!!};  right-inverse-of = {!!} } } }
  where
    |α|′ = |α| ⦃ fα ⦄
    |β|′ = |α| ⦃ fβ ⦄
\end{code}
