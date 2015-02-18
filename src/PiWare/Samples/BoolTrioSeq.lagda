\begin{code}
module PiWare.Samples.BoolTrioSeq where

open import Function using (id; _$_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Plugs.Core BoolTrio using (ALR⤪; swap⤪; _⟫⤪_; _|⤪_)
open import PiWare.Plugs BoolTrio using (swap⤨; fork×⤨)
open import PiWare.Circuit BoolTrio using (ℂ; plugℂ; delayℂ; _⟫_; _||_)
open import PiWare.Samples.BoolTrioComb using (⊥ℂ; ¬ℂ; ∨ℂ)
open import PiWare.Samples.Muxes using (mux)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()  -- only instances
open import PiWare.Synthesizable.Bool using ()  -- only instances
\end{code}


%<*shift>
\AgdaTarget{shift}
\begin{code}
shift : ℂ B B
shift = delayℂ swap⤨
\end{code}
%</shift>


%<*toggle>
\AgdaTarget{toggle}
\begin{code}
toggle : ℂ ⊤ B
toggle = ⊥ℂ ⟫ delayℂ (∨ℂ ⟫ ¬ℂ ⟫ fork×⤨)
\end{code}
%</toggle>


-- input × load → out
%<*reg>
\AgdaTarget{reg}
\begin{code}
reg : ℂ (B × B) B
reg = delayℂ (rearrange ⟫ mux ⟫ fork×⤨)
    where rearrange = plugℂ $    swap⤪ {1} {1} (λ ())  |⤪  id
                              ⟫⤪                 ALR⤪ {1} {1} {1}
                              ⟫⤪  id {A = Fin 1}  |⤪  swap⤪ {1} {1} (λ ())
\end{code}
%</reg>

