\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ)
open import PiWare.Samples.BoolTrioCombCore using (⊥ℂ'; ⊤ℂ'; ¬ℂ'; ∧ℂ'; ∨ℂ'; ¬∧ℂ'; ⊻ℂ'; hadd'; fadd')

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*fundamentals>
\AgdaTarget{⊥ℂ, ⊤ℂ, ¬ℂ, ∧ℂ, ∨ℂ}
\begin{code}
⊥ℂ ⊤ℂ : ℂX ⊤ B
⊥ℂ = Mkℂ ⊥ℂ'
⊤ℂ = Mkℂ ⊤ℂ'

¬ℂ : ℂX B B
¬ℂ = Mkℂ ¬ℂ'

∧ℂ ∨ℂ : ℂX (B × B) B
∧ℂ = Mkℂ ∧ℂ'
∨ℂ = Mkℂ ∨ℂ'
\end{code}
%</fundamentals>

%<*nand>
\AgdaTarget{¬∧ℂ}
\begin{code}
¬∧ℂ : ℂX (B × B) B
¬∧ℂ = Mkℂ ¬∧ℂ'
\end{code}
%</nand>

%<*xor>
\AgdaTarget{⊻ℂ}
\begin{code}
⊻ℂ : ℂX (B × B) B
⊻ℂ = Mkℂ ⊻ℂ'
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\AgdaTarget{hadd}
\begin{code}
hadd : ℂX (B × B) (B × B)
hadd = Mkℂ hadd'
\end{code}
%</hadd>


(a × b) × cin → co × s
%<*fadd>
\AgdaTarget{fadd}
\begin{code}
fadd : ℂX ((B × B) × B) (B × B)
fadd = Mkℂ fadd'
\end{code}
%</fadd>
