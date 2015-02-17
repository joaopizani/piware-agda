\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)

module PiWare.Gates (At : Atomic) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open Atomic At using (W)
\end{code}


%<*Gates>
\AgdaTarget{Gates, |Gates|, |in|, |out|, spec, Gates\#}
\begin{code}
record Gates : Set where
    field
        |Gates|    : ℕ
        |in| |out| : Fin |Gates| → ℕ
        spec       : (g# : Fin |Gates|) → (W (|in| g#) → W (|out| g#))

    Gates# = Fin |Gates|
\end{code}
%</Gates>
