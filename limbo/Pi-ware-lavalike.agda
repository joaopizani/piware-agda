module Pi-ware-lavalike where

open import Data.Vec using (Vec; head; map; foldr₁) renaming ([] to ε; _∷_ to _✧_)
open import Data.Nat using (ℕ; suc; zero)


data ℂ (α : Set) : Set where
    -- Fundamental computation constructors
    Not : ℂ α → ℂ α
    And : {n : ℕ} → Vec (ℂ α) (suc n) → ℂ α
    Or  : {n : ℕ} → Vec (ℂ α) (suc n) → ℂ α
    -- Binding-related
    Port : α → ℂ α  -- Var of PHOAS
    In   : (α → ℂ α) → ℂ α  -- Lambda of PHOAS

Circuit : Set₁
Circuit = ∀ {α} → ℂ α

input : ∀ {α} → (ℂ α → ℂ α) → ℂ α
input c = In (λ x → c (Port x))

open import Data.Bool using (Bool; _∧_; _∨_; not)
open import Function using (_∘_; _$_)

sampleNot : ℂ Bool
sampleNot = input Not

sampleAnd : ℂ Bool
sampleAnd = In (λ x →
            In (λ y →
                And (Port x ✧ Port y ✧ ε)))

-- TODO: the whole thing, but nicer
sampleXor : ℂ Bool
sampleXor = In (λ x →
            In (λ y →
                Or (
                  (And (Not (Port x) ✧ Port y ✧ ε)) ✧
                  (And (Port x ✧ Not (Port y) ✧ ε)) ✧ ε)))

-- evaluation stuck at a value type with **negative occurrences**
