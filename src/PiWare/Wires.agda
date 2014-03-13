module PiWare.Wires where

open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_)


-- Elements of this type describe the *structure* of circuit IO ports
data Wires : Set where
    ↿    : Wires
    _⊠_ : Wires → ℕ     → Wires
    _⊞_ : Wires → Wires → Wires

infixl 9 _⊠_
infixl 8 _⊞_


-- The size of a circuit's input (or output) interface
#_ : Wires → ℕ
# ↿        = 1
# (w ⊠ n) = suc n * (# w)
# (w ⊞ v) = (# w) + (# v)


-- Mapping elements of Wires to Agda types (universe construction)
⟬_⟭ : Wires → Set
⟬ ↿ ⟭ = ⊤
⟬ w ⊠ n ⟭ = Vec ⟬ w ⟭ (suc n)
⟬ w ⊞ v ⟭ = ⟬ w ⟭ ⊎ ⟬ v ⟭
