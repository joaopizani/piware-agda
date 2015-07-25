\begin{code}
module Data.FiniteType.Base where

open import Data.Nat.Base using (ℕ)
open import Data.Fin using (Fin)

open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Function.Bijection.Sets using (module Surjection′; _↠′_)
open import Data.Fin.Properties.Extra using (eq?ⁿ)
\end{code}


%<*Finite>
\AgdaTarget{Finite, |α|, left-inverse}
\begin{code}
record Finite {ℓ} (α : Set ℓ) : Set ℓ where
  field
    |α|         : ℕ
    surjection  : Fin |α| ↠′ α

  open Surjection′ surjection public
\end{code}
%</Finite>

%<*dec-eq-n>
\AgdaTarget{from↣, \_≟ⁿ\_}
\begin{code}
  _≟ⁿ_ : Decidable {A = α} _≡_
  _≟ⁿ_ = eq?ⁿ injection
\end{code}
%</dec-eq-n>

\begin{code}
  infix 4 _≟ⁿ_
\end{code}
