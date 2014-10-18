\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio; FalseConst#; TrueConst#; Not#; And#; Or#)
open import PiWare.Circuit.Core BoolTrio using (Gate)
open import PiWare.Plugs BoolTrio
    using (pFork×; pFork×^; pid; pid^; pALR; pALR^; pARL; pARL^; pFst; pFst^; pSnd; pSnd^)
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; _⟫_; _||_; _named_)
\end{code}


%<*fundamentals>
\begin{code}
⊥ℂ ⊤ℂ ⊤ℂ^ ⊥ℂ^ : ℂ ⊤ B
⊥ℂ^ = ⊥ℂ named "falseGate"
⊥ℂ = Mkℂ (Gate FalseConst#)

⊤ℂ^ = ⊤ℂ named "trueGate"
⊤ℂ = Mkℂ (Gate TrueConst#)

¬ℂ ¬ℂ^ : ℂ B B
¬ℂ^ = ¬ℂ named "notGate"
¬ℂ = Mkℂ (Gate Not#)

∧ℂ ∨ℂ ∧ℂ^ ∨ℂ^ : ℂ (B × B) B
∧ℂ^ = ∧ℂ named "andGate"
∧ℂ = Mkℂ (Gate And#) 

∨ℂ^ = ∨ℂ named "orGate"
∨ℂ = Mkℂ (Gate Or#)
\end{code}
%</fundamentals>

%<*nand>
\begin{code}
¬∧ℂ ¬∧ℂ^ : ℂ (B × B) B
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
¬∧ℂ^ = ∧ℂ^ ⟫ ¬ℂ^ named "nand"
\end{code}
%</nand>

%<*xor>
\begin{code}
⊻ℂ ⊻ℂ^ : ℂ (B × B) B
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ

⊻ℂ^ = c named "xor" where
  c =   pFork×^
      ⟫ (¬ℂ^ || pid^ ⟫ ∧ℂ^) || (pid^ || ¬ℂ^ ⟫ ∧ℂ^)
      ⟫ ∨ℂ^
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\begin{code}
hadd hadd^ : ℂ (B × B) (B × B)
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ

hadd^ = c named "hadd" where
  c =   pFork×^
      ⟫ ∧ℂ^ || ⊻ℂ^
\end{code}
%</hadd>

(a × b) × cin → co × s
%<*fadd>
\begin{code}
fadd fadd^ : ℂ ((B × B) × B) (B × B)
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid

fadd^ = c named "fadd" where
  c =   hadd^ || pid^
      ⟫      pALR^
      ⟫ pid^  || hadd^
      ⟫      pARL^
      ⟫ ∨ℂ^   || pid^
\end{code}
%</fadd>


-- TODO: Make it generic using the sum constructor.
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
%<*mux2to1>
\begin{code}
mux2to1 mux2to1^ : ℂ (B × (B × B)) B
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ

mux2to1^ = c named "mux2to1" where
  c =   pFork×^
      ⟫ (¬ℂ^ || pFst^ ⟫ ∧ℂ^) || (pid^ || pSnd^ ⟫ ∧ℂ^)
      ⟫ ∨ℂ^
\end{code}
%</mux2to1>
