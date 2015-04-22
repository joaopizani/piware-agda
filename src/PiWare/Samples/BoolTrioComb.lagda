\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Nat.Base using (_+_)

open import PiWare.Gates.BoolTrio using (BoolTrio; ⊥ℂ#; ⊤ℂ#; ¬ℂ#; ∧ℂ#; ∨ℂ#)
open import PiWare.Circuit {Gt = BoolTrio} using (𝐂; Gate; _⟫_; _∥_)
open import PiWare.Plugs BoolTrio using (id⤨; fork×⤨; ALR⤨; ARL⤨)
\end{code}


%<*fundamentals>
\AgdaTarget{⊥ℂ, ⊤ℂ, ¬ℂ, ∧ℂ, ∨ℂ}
\begin{code}
⊥ℂ ⊤ℂ : 𝐂 0 1
⊥ℂ = Gate ⊥ℂ#
⊤ℂ = Gate ⊤ℂ#

¬ℂ : 𝐂 1 1
¬ℂ = Gate ¬ℂ#

∧ℂ ∨ℂ : 𝐂 2 1
∧ℂ = Gate ∧ℂ#
∨ℂ = Gate ∨ℂ#
\end{code}
%<*fundamentals>


%<*nand>
\AgdaTarget{¬∧ℂ}
\begin{code}
¬∧ℂ : 𝐂 2 1
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}
%</nand>

%<*xor>
\AgdaTarget{⊻ℂ}
\begin{code}
⊻ℂ : 𝐂 2 1
⊻ℂ =   fork×⤨
      ⟫ (¬ℂ ∥ id⤨ {1} ⟫ ∧ℂ)  ∥  (id⤨ {1} ∥ ¬ℂ ⟫ ∧ℂ)
      ⟫                   ∨ℂ
\end{code}
%</xor>


-- a × b → c × s
%<*hadd>
\AgdaTarget{hadd}
\begin{code}
hadd : 𝐂 2 2
hadd =    fork×⤨
        ⟫ ∧ℂ ∥ ⊻ℂ
\end{code}
%</hadd>


-- (a × b) × cin → co × s
%<*fadd>
\AgdaTarget{fadd}
\begin{code}
fadd : 𝐂 (2 + 1) (1 + 1)
fadd =     hadd   ∥  id⤨
       ⟫     ALR⤨ {1} {1}
       ⟫  id⤨ {1} ∥ hadd
       ⟫     ARL⤨ {1} {1}
       ⟫      ∨ℂ   ∥  id⤨
\end{code}
%</fadd>
