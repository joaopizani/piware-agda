\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)

module PiWare.Gates (At : Atomic) where

open import Data.Nat.Base using (ℕ)
open import Data.Fin using (Fin)

open import PiWare.Interface using (Ix)
open Atomic At using (W)
\end{code}


%<*Gates>
\AgdaTarget{Gates, |Gates|, |in|, |out|, spec, Gate\#}
\begin{code}
record Gates : Set where
    field |Gates| : ℕ

    Gate# = Fin |Gates|

    field
        |in| |out|  : Gate# → Ix
        spec        : (g : Gate#) → (W (|in| g) → W (|out| g))
\end{code}
%</Gates>
