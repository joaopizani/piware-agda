\begin{code}
module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Nat using (suc; _⊔_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec; head) renaming ([_] to singleton)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B

import PiWare.Atom as A
open A.Atomic Atomic-B using (Atom#)
\end{code}


-- basic instance
\begin{code}
instance
\end{code}
%<*Synth-Bool>
\begin{code}
  ⇓W⇑-B : ⇓W⇑ B
  ⇓W⇑-B = ⇓W⇑[ singleton , head ]
\end{code}
%</Synth-Bool>
