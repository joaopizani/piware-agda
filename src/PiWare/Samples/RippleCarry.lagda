\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to B)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (ℂX; _⟫_; _||_)
open import PiWare.Plugs BoolTrio using (pid; pFst; pSwap; pCons; pUncons; pIntertwine; pALR; pARL)
open import PiWare.Samples.BoolTrioComb using (fadd)
\end{code}


-- cin × a × b → s × cout
%<*ripple>
\AgdaTarget{ripple}
\begin{code}
ripple : ∀ n →  let W = Vec B n  in  ℂX (B × W × W) (W × B)
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
