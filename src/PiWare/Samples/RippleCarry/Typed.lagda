\begin{code}
module PiWare.Samples.RippleCarry.Typed where

open import Data.Nat.Base using (_+_; _*_)
open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Bool.Base using () renaming (Bool to B)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Typed BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.RippleCarry using (ripple)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*ripple-typed>
\AgdaTarget{ripplê}
\begin{code}
ripplê : ∀ n →  let W = Vec B n  in  𝐂̂ (B × W × W) (W × B) {1 + (n * 1 + n * 1)} {n * 1 + 1}
ripplê n = Mkℂ̂ (ripple n)
\end{code}
%</ripple-typed>
