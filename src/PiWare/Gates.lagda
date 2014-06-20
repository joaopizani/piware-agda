\begin{code}
open import PiWare.Atom using (Atomic)

module PiWare.Gates (At : Atomic) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

open import PiWare.Synthesizable At using (𝕎)
\end{code}


%<*Gates>
\begin{code}
record Gates : Set where
    field
        |Gates|-1 : ℕ  -- needs to have at least one gate
        ins outs  : Fin (suc |Gates|-1) → ℕ
        spec      : (g : Fin (suc |Gates|-1)) → (𝕎 (ins g) → 𝕎 (outs g))

    |Gates| = suc |Gates|-1
    Gates#  = Fin |Gates|
\end{code}
%</Gates>
