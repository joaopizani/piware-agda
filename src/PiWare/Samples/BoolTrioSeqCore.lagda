\begin{code}
module PiWare.Samples.BoolTrioSeqCore where

open import Function using (id; _$_)
open import Data.Fin using (Fin)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Plug; DelayLoop; _⟫'_)
open import PiWare.Plugs.Functions using (_⟫⤪_; _|⤪_; swap⤪; ALR⤪)
open import PiWare.Plugs.Core BoolTrio using (swap⤨'; fork×⤨')
open import PiWare.Samples.BoolTrioCombCore using (¬ℂ'; ⊥ℂ'; ∨ℂ')
open import PiWare.Samples.MuxesCore using (mux')
\end{code}


%<*shift-core>
\AgdaTarget{shift'}
\begin{code}
shift' : ℂ' 1 1
shift' = DelayLoop (swap⤨' {1} {1})
\end{code}
%</shift-core>


%<*toggle-core>
\AgdaTarget{toggle'}
\begin{code}
toggle' : ℂ' 0 1 
toggle' = ⊥ℂ' ⟫' DelayLoop (∨ℂ' ⟫' ¬ℂ' ⟫' fork×⤨')
\end{code}
%</toggle-core>


-- input × load → out
%<*reg-core>
\AgdaTarget{reg'}
\begin{code}
reg' : ℂ' 2 1
reg' = DelayLoop (rearrange ⟫' mux' ⟫' fork×⤨')
    where rearrange = Plug $    swap⤪ {1} {1}   |⤪   id
                             ⟫⤪                 ALR⤪ {1} {1}
                             ⟫⤪  id {A = Fin 1}  |⤪   swap⤪ {1}
\end{code}
%</reg-core>
