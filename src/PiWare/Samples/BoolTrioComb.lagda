\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.BoolTrioCombCore using (⊥ℂ; ⊤ℂ; ¬ℂ; ∧ℂ; ∨ℂ; ¬∧ℂ; ⊻ℂ; hadd; fadd)
open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*fundamentals>
\AgdaTarget{⊥ℂ̂, ⊤ℂ̂, ¬ℂ̂, ∧ℂ̂, ∨ℂ̂}
\begin{code}
⊥ℂ̂ ⊤ℂ̂ : 𝐂̂ ⊤ B
⊥ℂ̂ = Mkℂ̂ ⊥ℂ
⊤ℂ̂ = Mkℂ̂ ⊤ℂ

¬ℂ̂ : 𝐂̂ B B
¬ℂ̂ = Mkℂ̂ ¬ℂ

∧ℂ̂ ∨ℂ̂ : 𝐂̂ (B × B) B
∧ℂ̂ = Mkℂ̂ ∧ℂ
∨ℂ̂ = Mkℂ̂ ∨ℂ
\end{code}
%</fundamentals>

%<*nand>
\AgdaTarget{¬∧ℂ̂}
\begin{code}
¬∧ℂ̂ : 𝐂̂ (B × B) B
¬∧ℂ̂ = Mkℂ̂ ¬∧ℂ
\end{code}
%</nand>

%<*xor>
\AgdaTarget{⊻ℂ̂}
\begin{code}
⊻ℂ̂ : 𝐂̂ (B × B) B
⊻ℂ̂ = Mkℂ̂ ⊻ℂ
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\AgdaTarget{hadd̂}
\begin{code}
hadd̂ : 𝐂̂ (B × B) (B × B)
hadd̂ = Mkℂ̂ hadd
\end{code}
%</hadd>


(a × b) × cin → co × s
%<*fadd>
\AgdaTarget{fadd̂}
\begin{code}
fadd̂ : 𝐂̂ ((B × B) × B) (B × B)
fadd̂ = Mkℂ̂ fadd
\end{code}
%</fadd>
