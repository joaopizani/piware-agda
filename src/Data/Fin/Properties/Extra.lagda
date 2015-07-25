\begin{code}
module Data.Fin.Properties.Extra where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)

open import Function.Bijection.Sets using (_↣′_)
open import Relation.Nullary.Decidable.Extra using (via-injection′)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


\begin{code}
eq?ⁿ : ∀ {n ℓ} {α : Set ℓ} → (α ↣′ Fin n) → Decidable {A = α} _≡_
eq?ⁿ inj = via-injection′ inj _≟_
\end{code}
