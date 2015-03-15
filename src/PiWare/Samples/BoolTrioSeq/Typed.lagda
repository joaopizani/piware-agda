\begin{code}
module PiWare.Samples.BoolTrioSeq.Typed where

open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Typed BoolTrio using (ℂ̂; Mkℂ̂)
open import PiWare.Samples.BoolTrioSeq using (shift; toggle; reg)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*shift-typed>
\AgdaTarget{shift̂}
\begin{code}
shift̂ : ℂ̂ B B
shift̂ = Mkℂ̂ shift
\end{code}
%</shift-typed>


%<*toggle-typed>
\AgdaTarget{togglê}
\begin{code}
togglê : ℂ̂ ⊤ B
togglê = Mkℂ̂ toggle
\end{code}
%</toggle-typed>


-- input × load → out
%<*reg-typed>
\AgdaTarget{reĝ}
\begin{code}
reĝ : ℂ̂ (B × B) B
reĝ = Mkℂ̂ reg
\end{code}
%</reg-typed>
