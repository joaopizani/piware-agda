\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Nat using (_+_; _*_)
open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Bool using () renaming (Bool to B)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.RippleCarryCore using (ripple)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*ripple>
\AgdaTarget{ripplê}
\begin{code}
ripplê : ∀ n →  let W = Vec B n  in  𝐂̂ (B × W × W) (W × B) {1 + (n * 1 + n * 1)} {n * 1 + 1}
ripplê n = Mkℂ̂ (ripple n)
\end{code}
%</ripple>
