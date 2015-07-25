\begin{code}
module Data.ElimFinite where

open import Function using (id; _$_; _∘_)
open import Data.Fin using (Fin)
open import Data.Vec using (tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.HVec using (vec↑; lookup′↑)

open import Relation.Binary.PropositionalEquality.Core using (subst)

open import Data.FiniteType.Base using (Finite; module Finite)
\end{code}

\begin{code}
open Finite ⦃ ... ⦄
\end{code}


\begin{code}
elimFin : ∀ {n} {P : Fin n → Set} {ps : vec↑ (tabulate P)} → (∀ i → P i)
elimFin {P = P} {ps = ps} i = subst id (lookup∘tabulate P i) $ lookup′↑ i ps
\end{code}


\begin{code}
elimFinite : ∀ {ℓ} {α : Set ℓ} {P : α → Set} ⦃ fin : Finite α ⦄ {ps : vec↑ (tabulate (P ∘ to))} → ∀ x → P x
elimFinite {P = P} ⦃ fin ⦄ {ps} x = subst P (right-inverse-of x) $ elimFin {P = P ∘ to} {ps} (from x)
\end{code}
