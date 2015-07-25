\begin{code}
module Relation.Nullary.Decidable.Extra where

open import Relation.Nullary using (yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import Function.Bijection.Sets using (module Injection′; _↣′_)
\end{code}


\begin{code}
module _ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} where
 open Injection′
\end{code}

\begin{code}
 via-injection′ : (α ↣′ β) → Decidable {A = β} _≡_ → Decidable {A = α} _≡_
 via-injection′ inj _≟β_ x y with (to inj x) ≟β (to inj y)
 ... | yes injX≡injY = yes (injective inj injX≡injY)
 ... | no  injX≢injY = no (λ x≡y → injX≢injY (cong (to inj) x≡y))
\end{code}
