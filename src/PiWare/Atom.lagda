\begin{code}
module PiWare.Atom where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

open import Function.Bijection.Sets using (_↔′_; module Inverse′)
open import Data.FiniteType.Base using (Finite)
\end{code}


%<*Atomic>
\AgdaTarget{Atomic, Atom, |Atom|-1, enum, |Atom|, Atom\#, W}
\begin{code}
record Atomic : Set₁ where
    field |Atom|-1 : ℕ

    |Atom| = suc |Atom|-1
    Atom#  = Fin |Atom|

    field  Atom  : Set
           enum  : Atom# ↔′ Atom

    W = Vec Atom

    open Inverse′ enum public
\end{code}
%</Atomic>


\begin{code}
open Atomic ⦃ … ⦄
\end{code}


%<*Finite-Atomic>
\AgdaTargeT{Finite-Atomic}
\begin{code}
instance
 Finite-Atomic : ⦃ At : Atomic ⦄ → Finite Atom
 Finite-Atomic ⦃ At ⦄ = record { |α| = |Atom|
                               ; surjection = record { to = to
                                                     ; surjective = record { from = from
                                                                           ; right-inverse-of = right-inverse-of } } }
\end{code}
%</Finite-Atomic>
