\begin{code}
module PiWare.Samples.BoolTrioSeq where

open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (ℂ̂; Mkℂ̂)
open import PiWare.Samples.BoolTrioSeqCore using (shift; toggle; reg)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()  -- only instances
open import PiWare.Synthesizable.Bool using ()  -- only instances
\end{code}


%<*shift>
\AgdaTarget{shift̂}
\begin{code}
shift̂ : ℂ̂ B B
shift̂ = Mkℂ̂ shift
\end{code}
%</shift>


%<*toggle>
\AgdaTarget{togglê}
\begin{code}
togglê : ℂ̂ ⊤ B
togglê = Mkℂ̂ toggle
\end{code}
%</toggle>


-- input × load → out
%<*reg>
\AgdaTarget{reĝ}
\begin{code}
reĝ : ℂ̂ (B × B) B
reĝ = Mkℂ̂ reg
\end{code}
%</reg>
