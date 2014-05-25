module PiWare.Atom where

open import Data.Bool using (false; true) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≤_)
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality using (_≡_)


record AtomInfo : Set₁ where
    field
        -- primitives
        Atom   : Set
        card   : ℕ
        atom#  : Fin card → Atom
        𝔹→atom : 𝔹 → Atom
        atom→𝔹 : Atom → 𝔹

        -- axioms
        inv-atom𝔹 : ∀ b → atom→𝔹 (𝔹→atom b ) ≡ b
        card≥2 : 2 ≤ card
        inj-atom# : ∀ a₁ a₂ → atom# a₁ ≡ atom# a₂ → a₁ ≡ a₂

    trueA : Atom
    trueA = 𝔹→atom true

    falseA : Atom
    falseA = 𝔹→atom false
