\begin{code}
module PiWare.Circuit.Applicative where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool.Base using (Bool)
open import Data.Vec using (Vec)
\end{code}


\begin{code}
W : ℕ → Set
W = Vec Bool

data ℂ : ℕ → ℕ → Set where
  PURE : ∀ {n} → W n → ℂ 0 n
  ID : ∀ {n} → ℂ n n
  AND OR : ℂ 2 1
  NOT : ℂ 1 1
  _⟫_ : ∀ {a b c}    → ℂ a b → ℂ b c → ℂ a c
  _∥_ : ∀ {a b c d}  → ℂ a b → ℂ c d → ℂ (a + c) (b + d)


pure : ∀ {n} → W n → ℂ 0 n
pure = PURE


-- _⊗_ : ℂ (a → b) → ℂ a → ℂ b
_⊗_ : ∀ {a b m n} → ℂ (a + n) b → ℂ m a → ℂ (m + n) b
_⊗_ cab ca = (ca ∥ ID) ⟫ cab

\end{code}
