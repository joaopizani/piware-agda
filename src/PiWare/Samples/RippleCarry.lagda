\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to B)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio
open import PiWare.Plugs BoolTrio

open import PiWare.Samples.BoolTrio using (fadd)
\end{code}


cin × a × b → s × cout
%<*ripple>
\begin{code}
ripple : (n : ℕ) →  let W = Vec B n  in  ℂ (B × W × W) (W × B)
ripple zero    = pid || pFst ⟫ pSwap
ripple (suc m) =
      pid   || (pUncons || pUncons ⟫ pIntertwine)
    ⟫     pAssoc
    ⟫ fadd  || pid
    ⟫      pALR
    ⟫ pid   || ripple m
    ⟫      pARL
    ⟫ pCons || pid
    where pAssoc = pARL ⟫ pARL || pid
\end{code}
%</ripple>
