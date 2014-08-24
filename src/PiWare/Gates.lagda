\begin{code}
open import PiWare.Atom using (Atomic)

module PiWare.Gates (At : Atomic) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import PiWare.Synthesizable At using (W)
\end{code}


%<*Gates>
\begin{code}
record Gates : Set where
    field
        |Gates|     : ℕ
        |in| |out|  : Fin |Gates| → ℕ
        spec        :  (g : Fin |Gates|)
                       → (W (|in| g) → W (|out| g))

    Gates#   = Fin |Gates|
\end{code}
%</Gates>
