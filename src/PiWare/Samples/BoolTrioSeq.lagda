\begin{code}
module PiWare.Samples.BoolTrioSeq where

open import Function using (id; _$_)
open import Data.Fin using (Fin)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit {Gt = BoolTrio} using (ℂ; Plug; DelayLoop; _⟫_)
open import PiWare.Plugs.Core using (_⟫⤪_; _|⤪_; id⤪; swap⤪; ALR⤪)
open import PiWare.Plugs BoolTrio using (swap⤨; fork×⤨)
open import PiWare.Samples.BoolTrioComb using (¬ℂ; ⊥ℂ; ∨ℂ)
open import PiWare.Samples.Muxes using (mux)
\end{code}


%<*shift>
\AgdaTarget{shift}
\begin{code}
shift : ℂ 1 1
shift = DelayLoop (swap⤨ {1} {1})
\end{code}
%</shift>


%<*toggle>
\AgdaTarget{toggle}
\begin{code}
toggle : ℂ 0 1 
toggle = ⊥ℂ ⟫ DelayLoop (∨ℂ ⟫ ¬ℂ ⟫ fork×⤨)
\end{code}
%</toggle>


-- input × load → out
%<*reg>
\AgdaTarget{reg}
\begin{code}
reg : ℂ 2 1
reg = DelayLoop (rearrange ⟫ mux ⟫ fork×⤨)
    where rearrange = Plug $    swap⤪ {1} {1} |⤪   id⤪
                             ⟫⤪          ALR⤪ {1} {1}
                             ⟫⤪ id⤪ {1}       |⤪   swap⤪ {1}
\end{code}
%</reg>
