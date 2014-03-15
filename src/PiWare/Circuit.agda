module PiWare.Circuit where

open import Function using (id)
open import Data.Sum using (inj₁; inj₂)
open import PiWare.Wires


-- Core Circuit type
data ℂ (α : Set) : Wires → Wires → Set where
    Not : ℂ α ↿ ↿
    And : ℂ α (↿ ⊞ ↿) ↿
    Or  : ℂ α (↿ ⊞ ↿) ↿
    Plug : ∀ {i o} → (f : ⟬ o ⟭ → ⟬ i ⟭) → ℂ α i o
    _⟫_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : ∀ {i₁ o₁ i₂ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ ⊞ i₂) (o₁ ⊞ o₂)

infixl 5 _||_
infixl 4 _⟫_


-- "Smart constructors", specific instances of serial and (specially) parallel
-- composition to avoid having to pass arguments which should be implicit
