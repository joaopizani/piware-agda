\begin{code}
module PiWare.Samples.BoolTrioSeq where

open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Plugs BoolTrio using (pid; pALR; pARL; pSwap; pFork×)
open import PiWare.Circuit BoolTrio using (ℂ; delayℂ; _⟫_; _||_; _named_)
open import PiWare.Samples.BoolTrioComb using (⊥ℂ; ¬ℂ; ∨ℂ; mux2to1)
\end{code}


%<*shift>
\AgdaTarget{shift}
\begin{code}
shift : ℂ B B
shift = delayℂ pSwap
\end{code}
%</shift>

%<*toggle>
\AgdaTarget{toggle}
\begin{code}
toggle : ℂ ⊤ B
toggle = ⊥ℂ ⟫ delayℂ (∨ℂ ⟫ ¬ℂ ⟫ pFork×)
\end{code}
%</toggle>

-- input × load → out
%<*reg>
\AgdaTarget{reg}
\begin{code}
reg : ℂ (B × B) B
reg = delayℂ comb
    where rearrange = pSwap || pid  ⟫  pALR  ⟫  pid || pSwap
          comb      = rearrange  ⟫  mux2to1  ⟫  pFork×
\end{code}
%</reg>

