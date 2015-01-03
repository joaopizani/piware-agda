\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import PiWare.Atom.Bool using (Atomic-B; False#; True#)
open import PiWare.Gates.BoolTrio using (BoolTrio; FalseConst#; TrueConst#; Not#; And#; Or#)
open import PiWare.Circuit.Core BoolTrio using (Gate)
open import PiWare.Plugs BoolTrio using (pFork×; pid; pALR; pARL; pFst; pSnd)
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; _⟫_; _||_; |+; _named_)

open import PiWare.Synthesizable Atomic-B using ()  -- only instances
open import PiWare.Synthesizable.Bool using ()  -- only instances
\end{code}


%<*fundamentals>
\AgdaTarget{⊥ℂ, ⊤ℂ, ¬ℂ, ∧ℂ, ∨ℂ}
\begin{code}
⊥ℂ ⊤ℂ : ℂ ⊤ B
⊥ℂ = Mkℂ (Gate FalseConst#) named "⊥ℂ"
⊤ℂ = Mkℂ (Gate TrueConst#) named "⊤ℂ"

¬ℂ : ℂ B B
¬ℂ = Mkℂ (Gate Not#) named "¬ℂ"

∧ℂ ∨ℂ : ℂ (B × B) B
∧ℂ = Mkℂ (Gate And#) named "∧ℂ"
∨ℂ = Mkℂ (Gate Or#) named "∨ℂ"
\end{code}
%</fundamentals>

%<*nand>
\AgdaTarget{¬∧ℂ}
\begin{code}
¬∧ℂ : ℂ (B × B) B
¬∧ℂ = ∧ℂ ⟫ ¬ℂ named "¬∧ℂ"
\end{code}
%</nand>

%<*xor>
\AgdaTarget{⊻ℂ}
\begin{code}
⊻ℂ : ℂ (B × B) B
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ
     named "⊻ℂ"
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\AgdaTarget{hadd}
\begin{code}
hadd : ℂ (B × B) (B × B)
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ
       named "hadd"
\end{code}
%</hadd>

(a × b) × cin → co × s
%<*fadd>
\AgdaTarget{fadd}
\begin{code}
fadd : ℂ ((B × B) × B) (B × B)
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid
       named "fadd"
\end{code}
%</fadd>


%<*mux2to1>
\AgdaTarget{mux2to1}
\begin{code}
mux2to1 : ℂ (B × (B × B)) B
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ
          named "mux2to1"
\end{code}
%</mux2to1>
