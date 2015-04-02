\begin{code}
module PiWare.Samples.Muxes where

open import Function using (_∘_)
open import Data.Nat using (zero; suc; _+_)
open import Data.Fin using (Fin)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (𝐂; _⟫_; _∥_; Plug)
open import PiWare.Plugs BoolTrio using (fork×⤨; nil⤨; id⤨; fst⤨; snd⤨)
open import PiWare.Plugs.Core using (_⤪_; _⟫⤪_; _|⤪_; id⤪; fork×⤪; ALR⤪; ARL⤪; intertwine⤪; swap⤪)
open import PiWare.Samples.BoolTrioComb using (¬ℂ; ∧ℂ; ∨ℂ)
\end{code}


%<*mux>
\AgdaTarget{mux}
\begin{code}
mux : 𝐂 3 1  -- s × (a × b) → c
mux =
                               fork×⤨
      ⟫ (¬ℂ ∥ fst⤨ {1} {1} ⟫ ∧ℂ)  ∥  (id⤨ {1} ∥ snd⤨ {1} ⟫ ∧ℂ)
      ⟫                          ∨ℂ
\end{code}
%</mux>


\begin{code}
adapt⤪ : ∀ n → (1 + ((1 + n) + (1 + n))) ⤪ ((1 + 1 + 1) + (1 + (n + n)))
adapt⤪ n =
                      fork×⤪ {1}     |⤪    id⤪ {(1 + n) + (1 + n)}
    ⟫⤪                   id⤪ {2}     |⤪    intertwine⤪ {1} {n} {1} {n}
    ⟫⤪                     ARL⤪ {1 + 1} {1 + 1} {n + n}
    ⟫⤪ intertwine⤪ {1} {1} {1} {1}   |⤪    id⤪
    ⟫⤪  (id⤪ {2} |⤪ swap⤪ {1} {1})  |⤪    id⤪ {n + n}
    ⟫⤪        ARL⤪ {1 + 1} {1} {1}   |⤪    id⤪
    ⟫⤪                      ALR⤪ {1 + 1 + 1} {1} {n + n}

adapt⤨ : ∀ n → 𝐂 (1 + ((1 + n) + (1 + n))) ((1 + 1 + 1) + (1 + (n + n)))
adapt⤨ = Plug ∘ adapt⤪
\end{code}

%<*muxN>
\AgdaTarget{muxN}
\begin{code}
muxN : ∀ n → 𝐂 (1 + (n + n)) n
muxN zero    = nil⤨
muxN (suc n) = adapt⤨ n  ⟫  mux ∥ muxN n
\end{code}
%</muxN>
