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
    field
        |Gates|    : ℕ
        |in| |out| : Fin |Gates| → Ix
        spec       : (g : Fin |Gates|) → (W (|in| g) → W (|out| g))

    Gate# = Fin |Gates|
\end{code}
%</Gates>
