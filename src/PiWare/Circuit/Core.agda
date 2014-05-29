module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)

open import PiWare.Atom


-- Purely combinational
data ℂ' (AI : AtomInfo) : ℕ → ℕ → Set where
    -- Fundamental gates
    Not : ℂ' AI 1 1
    And : ℂ' AI 2 1
    Or  : ℂ' AI 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' AI i o
    _⟫'_ : {i m o : ℕ} → ℂ' AI i m → ℂ' AI m o → ℂ' AI i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' AI i₁ o₁ → ℂ' AI i₂ o₂ → ℂ' AI (i₁ + i₂) (o₁ + o₂)
    _|+'_ : {i₁ i₂ o : ℕ} → ℂ' AI i₁ o → ℂ' AI i₂ o → ℂ' AI (suc (i₁ ⊔ i₂)) o
    
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_


-- Sequential
data ℂ'* (AI : AtomInfo) : ℕ → ℕ → Set where
    -- Embedding combinational circuits into the sequential setting
    Comb      : {i o : ℕ} → ℂ' AI i o → ℂ'* AI i o
    DelayLoop : {i o l : ℕ} → ℂ' AI (i + l) (o + l) → ℂ'* AI i o
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ'* AI i o
    _⟫'*_ : {i m o : ℕ} → ℂ'* AI i m → ℂ'* AI m o → ℂ'* AI i o
    _|'*_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ'* AI i₁ o₁ → ℂ'* AI i₂ o₂ → ℂ'* AI (i₁ + i₂) (o₁ + o₂)
    _|+'*_ : {i₁ i₂ o : ℕ} → ℂ'* AI i₁ o → ℂ'* AI i₂ o → ℂ'* AI (suc (i₁ ⊔ i₂)) o

infixr 5 _|'*_
infixr 5 _|+'*_
infixl 4 _⟫'*_
