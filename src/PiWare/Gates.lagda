\begin{code}
open import PiWare.Atom using (Atomic)

module PiWare.Gates (At : Atomic) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)

open import PiWare.Synthesizable At using (W)

import VHDL.AST as VHDL using (EntityDecl; ArchBody)
\end{code}


%<*Gates>
\begin{code}
record Gates : Set where
    field
        |Gates|    : ℕ
        |in| |out| : Fin |Gates| → ℕ
        spec       : (g : Fin |Gates|) → (W (|in| g) → W (|out| g))
        
        -- TODO: Arch depends on entity; sizing
        syn        : (g : Fin |Gates|) → VHDL.EntityDecl × VHDL.ArchBody

    Gates#   = Fin |Gates|
\end{code}
%</Gates>
