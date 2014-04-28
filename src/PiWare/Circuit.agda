module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)


-- Core Circuit type
data ℂ (α : Set) : ℕ → ℕ → Set where
    -- Fundamental building blocks
    Not : ℂ α 1 1
    And : ℂ α 2 1
    Or  : ℂ α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ α i o
    _⟫_  : {i m o : ℕ} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ + i₂) (o₁ + o₂)

infixl 5 _||_
infixl 4 _⟫_

-- "Algebra" for evaluating a circuit, closely related to the ℂ type itself.
-- Each field of the algebra corresponds to a "fundamental" constructor of ℂ
record Algℂ (α : Set) : Set where
   constructor algℂ[_,_,_]
   field
       ¬ : α → α
       ∧ : α → α → α
       ∨ : α → α → α


-- "Smart constructors", specific instances of serial and (specially) parallel
-- composition to avoid having to pass arguments which should be implicit
