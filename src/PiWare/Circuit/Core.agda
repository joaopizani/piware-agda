module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)


-- Core Circuit types

-- Purely combinational
data Combℂ (α : Set) : ℕ → ℕ → Set where
    -- Fundamental building blocks
    Not : Combℂ α 1 1
    And : Combℂ α 2 1
    Or  : Combℂ α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → Combℂ α i o
    _>>_ : {i m o : ℕ} → Combℂ α i m → Combℂ α m o → Combℂ α i o
    _><_ : {i₁ o₁ i₂ o₂ : ℕ} → Combℂ α i₁ o₁ → Combℂ α i₂ o₂ → Combℂ α (i₁ + i₂) (o₁ + o₂)
    
infixr 5 _><_
infixl 4 _>>_

-- Sequential
data Coreℂ (α : Set) : ℕ → ℕ → Set where
    -- Embedding combinational circuits into the sequential setting
    Comb : {i o : ℕ} → Combℂ α i o → Coreℂ α i o
    Delayed : {i o l : ℕ} → Combℂ α (i + l) (o + l) → Coreℂ α i o
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → Coreℂ α i o
    _>>_ : {i m o : ℕ} → Coreℂ α i m → Coreℂ α m o → Coreℂ α i o
    _><_ : {i₁ o₁ i₂ o₂ : ℕ} → Coreℂ α i₁ o₁ → Coreℂ α i₂ o₂ → Coreℂ α (i₁ + i₂) (o₁ + o₂)
