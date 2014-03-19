module PiWare.Circuit where

open import Function using (id)
open import Data.Sum using (inj₁; inj₂)
open import PiWare.Wires


-- Core Circuit type
data ℂ (α : Set) : Wires → Wires → Set where
    -- Fundamental building blocks
    Not : ℂ α ↿ ↿
    And : ℂ α (↿ ⊞ ↿) ↿
    Or  : ℂ α (↿ ⊞ ↿) ↿
    -- Structure-related
    Plug : ∀ {i o} → (f : ⟬ o ⟭ → ⟬ i ⟭) → ℂ α i o
    _⟫_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : ∀ {i₁ o₁ i₂ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ ⊞ i₂) (o₁ ⊞ o₂)

infixl 5 _||_
infixl 4 _⟫_

-- "Algebra" for evaluation of a circuit, closely related to the ℂ datatype itself.
-- Each field of the algebra corresponds to a "fundamental" constructor of ℂ
record Algℂ (α : Set) : Set where
   constructor algℂ[_,_,_]
   field
       ¬ : α → α
       ∧ : α → α → α
       ∨ : α → α → α

-- "Smart constructors", specific instances of serial and (specially) parallel
-- composition to avoid having to pass arguments which should be implicit
