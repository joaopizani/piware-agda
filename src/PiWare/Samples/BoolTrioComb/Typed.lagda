\begin{code}
module PiWare.Samples.BoolTrioComb.Typed where

open import Data.Bool.Base using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit.Base using (⊤)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Typed BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.BoolTrioComb using (⊥ℂ; ⊤ℂ; ¬ℂ; ∧ℂ; ∨ℂ; ¬∧ℂ; ⊻ℂ; hadd; fadd)
open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
\end{code}


%<*fundamentals-typed>
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
%</fundamentals-typed>

%<*nand-typed>
\AgdaTarget{¬∧ℂ̂}
\begin{code}
¬∧ℂ̂ : 𝐂̂ (B × B) B
¬∧ℂ̂ = Mkℂ̂ ¬∧ℂ
\end{code}
%</nand-typed>

%<*xor-typed>
\AgdaTarget{⊻ℂ̂}
\begin{code}
⊻ℂ̂ : 𝐂̂ (B × B) B
⊻ℂ̂ = Mkℂ̂ ⊻ℂ
\end{code}
%</xor-typed>


a × b → c × s
%<*hadd-typed>
\AgdaTarget{hadd̂}
\begin{code}
hadd̂ : 𝐂̂ (B × B) (B × B)
hadd̂ = Mkℂ̂ hadd
\end{code}
%</hadd-typed>


(a × b) × cin → co × s
%<*fadd-typed>
\AgdaTarget{fadd̂}
\begin{code}
fadd̂ : 𝐂̂ ((B × B) × B) (B × B)
fadd̂ = Mkℂ̂ fadd
\end{code}
%</fadd-typed>
