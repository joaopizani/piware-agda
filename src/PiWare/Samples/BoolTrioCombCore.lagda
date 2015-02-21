\begin{code}
module PiWare.Samples.BoolTrioCombCore where

open import Data.Nat using (_+_)

open import PiWare.Gates.BoolTrio using (BoolTrio; ⊥ℂ#; ⊤ℂ#; ¬ℂ#; ∧ℂ#; ∨ℂ#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'X; Gate; _⟫'_; _|'_)
open import PiWare.Plugs.Core BoolTrio using (id⤨'; fork×⤨'; ALR⤨'; ARL⤨')
\end{code}


%<*fundamentals-core>
\AgdaTarget{⊥ℂ', ⊤ℂ', ¬ℂ', ∧ℂ', ∨ℂ'}
\begin{code}
⊥ℂ' ⊤ℂ' : ℂ'X 0 1
⊥ℂ' = Gate ⊥ℂ#
⊤ℂ' = Gate ⊤ℂ#

¬ℂ' : ℂ'X 1 1
¬ℂ' = Gate ¬ℂ#

∧ℂ' ∨ℂ' : ℂ'X 2 1
∧ℂ' = Gate ∧ℂ#
∨ℂ' = Gate ∨ℂ#
\end{code}
%<*fundamentals-core>


%<*nand-core>
\AgdaTarget{¬∧ℂ'}
\begin{code}
¬∧ℂ' : ℂ'X 2 1
¬∧ℂ' = ∧ℂ' ⟫' ¬ℂ'
\end{code}
%</nand-core>

%<*xor-core>
\AgdaTarget{⊻ℂ'}
\begin{code}
⊻ℂ' : ℂ'X 2 1
⊻ℂ' =   fork×⤨'
      ⟫' (¬ℂ' |' id⤨' {1} ⟫' ∧ℂ')  |'  (id⤨' {1} |' ¬ℂ' ⟫' ∧ℂ')
      ⟫'                   ∨ℂ'
\end{code}
%</xor-core>


-- a × b → c × s
%<*hadd-core>
\AgdaTarget{hadd'}
\begin{code}
hadd' : ℂ'X 2 2
hadd' =    fork×⤨'
        ⟫' ∧ℂ' |' ⊻ℂ'
\end{code}
%</hadd-core>


-- (a × b) × cin → co × s
%<*fadd-core>
\AgdaTarget{fadd'}
\begin{code}
fadd' : ℂ'X (2 + 1) (1 + 1)
fadd' =       hadd'  |'  id⤨'
        ⟫'     ALR⤨' {1} {1}
        ⟫'  id⤨' {1} |' hadd'
        ⟫'     ARL⤨' {1} {1}
        ⟫'      ∨ℂ'   |'  id⤨'
\end{code}
%</fadd-core>
