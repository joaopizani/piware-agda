\begin{code}
module PiWare.Atom where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

open import Function.Bijection.Sets using (_↔′_)
\end{code}




%<*Atomic>
\AgdaTarget{Atomic, Atom, |Atom|-1, enum, |Atom|, Atom\#, W}
\begin{code}
record Atomic : Set₁ where
    field
        Atom     : Set
        |Atom|-1 : ℕ

        enum     : Fin (suc |Atom|-1) ↔′ Atom

    |Atom| = suc |Atom|-1
    Atom#  = Fin |Atom|
    W = Vec Atom
\end{code}
%</Atomic>
