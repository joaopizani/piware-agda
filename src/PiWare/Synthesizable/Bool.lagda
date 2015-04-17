\begin{code}
module PiWare.Synthesizable.Bool where

open import Data.Bool.Base using () renaming (Bool to B)
open import Data.Vec using (head) renaming ([_] to singleton)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑; ⇓W⇑[_,_])
\end{code}


-- basic instance
\begin{code}
instance
\end{code}
%<*Synth-Bool>
\AgdaTarget{⇓W⇑-B}
\begin{code}
 ⇓W⇑-B : ⇓W⇑ B
 ⇓W⇑-B = ⇓W⇑[ singleton , head ]
\end{code}
%</Synth-Bool>
