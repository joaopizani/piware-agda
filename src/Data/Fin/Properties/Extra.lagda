\begin{code}
module Data.Fin.Properties.Extra where

open import Data.Nat.Base using (ℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)

open import Function.Injection using (_↣_)
open import Relation.Binary.PropositionalEquality using (→-to-⟶)
\end{code}


\begin{code}
toℕ↣ : ∀ {n} → Fin n ↣ ℕ
toℕ↣ = record { to = →-to-⟶ toℕ; injective = toℕ-injective }
\end{code}
