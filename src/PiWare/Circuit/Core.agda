module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)


-- Purely combinational
data ℂ' (α : Set) : ℕ → ℕ → Set where
    -- Fundamental gates
    Not : ℂ' α 1 1
    And : ℂ' α 2 1
    Or  : ℂ' α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' α i o
    _⟫'_ : {i m o : ℕ} → ℂ' α i m → ℂ' α m o → ℂ' α i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' α i₁ o₁ → ℂ' α i₂ o₂ → ℂ' α (i₁ + i₂) (o₁ + o₂)
    _|+_ : {i₁ i₂ o : ℕ} → ℂ' α i₁ o → ℂ' α i₂ o → ℂ' α (suc (i₁ ⊔ i₂)) o
    
infixr 5 _|'_
infixl 4 _⟫'_

-- Sequential
data ℂ'* (α : Set) : ℕ → ℕ → Set where
    -- Embedding combinational circuits into the sequential setting
    Comb      : {i o : ℕ} → ℂ' α i o → ℂ'* α i o
    DelayLoop : {i o l : ℕ} → ℂ' α (i + l) (o + l) → ℂ'* α i o
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ'* α i o
    _⟫'*_ : {i m o : ℕ} → ℂ'* α i m → ℂ'* α m o → ℂ'* α i o
    _|'*_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ'* α i₁ o₁ → ℂ'* α i₂ o₂ → ℂ'* α (i₁ + i₂) (o₁ + o₂)
    _|+*_ : {i₁ i₂ o : ℕ} → ℂ'* α i₁ o → ℂ'* α i₂ o → ℂ'* α (suc (i₁ ⊔ i₂)) o

infixr 5 _|'*_
infixl 4 _⟫'*_
