\begin{code}
module PiWare.Samples.AndN where

open import Function using (id)

open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ)
open import PiWare.Samples.AndNCore using (andN')

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑[_,_])
open import PiWare.Synthesizable.Bool using ()
\end{code}



%<*andN>
\AgdaTarget{andN}
\begin{code}
andN : ∀ n → ℂX (Vec B n) B
andN k = Mkℂ ⦃ sα = ⇓W⇑[ id , id ] ⦄ (andN' k)
\end{code}
%</andN>
