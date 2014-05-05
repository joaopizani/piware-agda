module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)


-- Core Circuit type
data Coreℂ (α : Set) : ℕ → ℕ → Set where
    -- Fundamental building blocks
    Not : Coreℂ α 1 1
    And : Coreℂ α 2 1
    Or  : Coreℂ α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → Coreℂ α i o
    _>>_ : {i m o : ℕ} → Coreℂ α i m → Coreℂ α m o → Coreℂ α i o
    _><_ : {i₁ o₁ i₂ o₂ : ℕ} → Coreℂ α i₁ o₁ → Coreℂ α i₂ o₂ → Coreℂ α (i₁ + i₂) (o₁ + o₂)

infixr 5 _><_
infixl 4 _>>_
