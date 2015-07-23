\begin{code}
module Data.Fin.Properties.Extra where

open import Data.Nat.Base using (ℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (_≟_)

open import Function.Injection using (_↣_)
open import Relation.Nullary.Decidable using (via-injection)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; →-to-⟶)
\end{code}


\begin{code}
eq?ⁿ : ∀ {n ℓ} {α : Set ℓ} → (α ↣ Fin n) → Decidable {A = α} _≡_
eq?ⁿ inj = via-injection inj _≟_
\end{code}
