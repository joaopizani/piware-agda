\begin{code}
module Data.FiniteType where

open import Level using (_⊔_)

open import Data.Product using (_×_; map)
open import Data.FiniteType.Base using (Finite; module Finite)
\end{code}


\begin{code}
open Finite ⦃ ... ⦄
\end{code}


\begin{code}
Finite-× : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} ⦃ fα : Finite {ℓ₁} α ⦄ ⦃ fβ : Finite {ℓ₂} β ⦄ → Finite {ℓ₁ ⊔ ℓ₂} (α × β)
Finite-× ⦃ fα ⦄ ⦃ fβ ⦄ = record { to = {!map to to!};  from = {!!};  to∘from = {!!} }

\end{code}
