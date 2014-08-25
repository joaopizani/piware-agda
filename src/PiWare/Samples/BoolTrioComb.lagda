\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Nat using (zero; suc)
open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Unit using (⊤)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio; FalseConst#; TrueConst#; Not#; And#; Or#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _⟫'_; _|'_)
open import PiWare.Plugs BoolTrio using (pFork×; pid; pALR; pARL; pFst; pSnd)
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; _⟫_; _||_)
open import PiWare.Patterns BoolTrio using (seqsN)
\end{code}


%<*constants>
\begin{code}
⊥ℂ ⊤ℂ : ℂ ⊤ B
⊥ℂ = Mkℂ (Gate FalseConst#)
⊤ℂ = Mkℂ (Gate TrueConst#)
\end{code}
%</constants>

%<*booltrio>
\begin{code}
¬ℂ : ℂ B B
∧ℂ ∨ℂ : ℂ (B × B) B

¬ℂ = Mkℂ (Gate Not#)
∧ℂ = Mkℂ (Gate And#) 
∨ℂ = Mkℂ (Gate Or#)
\end{code}
%</booltrio>


%<*idN>
\begin{code}
idNℂ : ∀ n → ℂ B B
idNℂ n = seqsN n pid
\end{code}
%</idN>


%<*nand>
\begin{code}
¬∧ℂ : ℂ (B × B) B
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}
%</nand>

\begin{code}
idℂ = pid
\end{code}
%<*xor>
\begin{code}
⊻ℂ : ℂ (B × B) B
⊻ℂ =  pFork×
      ⟫ (¬ℂ || idℂ ⟫ ∧ℂ) || (idℂ || ¬ℂ ⟫ ∧ℂ)
      ⟫ ∨ℂ
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\begin{code}
hadd : ℂ (B × B) (B × B)
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ
\end{code}
%</hadd>

(a × b) × cin → co × s
%<*fadd>
\begin{code}
fadd : ℂ ((B × B) × B) (B × B)
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid
\end{code}
%</fadd>


-- TODO: Make it generic using the sum constructor.
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
%<*mux2to1>
\begin{code}
mux2to1 : ℂ (B × (B × B)) B
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ
\end{code}
%</mux2to1>
