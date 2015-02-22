\begin{code}
module PiWare.Samples.MuxesCore where

open import Function using (id; _∘_)
open import Data.Nat using (zero; suc; _+_)
open import Data.Fin using (Fin)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Core BoolTrio using (𝐂; _⟫_; _∥_; Plug; Nil)
open import PiWare.Plugs.Core BoolTrio using (fork×⤨; id⤨; fst⤨; snd⤨)
open import PiWare.Plugs.Functions using (_⟫⤪_; _|⤪_; fork×⤪; ALR⤪; ARL⤪; intertwine⤪; swap⤪)
open import PiWare.Samples.BoolTrioCombCore using (¬ℂ; ∧ℂ; ∨ℂ)
\end{code}


%<*mux-core>
\AgdaTarget{mux}
\begin{code}
mux : 𝐂 3 1  -- s × (a × b) → c
mux =
                               fork×⤨
      ⟫ (¬ℂ ∥ fst⤨ {1} {1} ⟫ ∧ℂ)  ∥  (id⤨ {1} ∥ snd⤨ {1} ⟫ ∧ℂ)
      ⟫                          ∨ℂ
\end{code}
%</mux-core>


\begin{code}
adapt⤪ : ∀ n → Fin ((1 + 1 + 1) + (1 + (n + n))) → Fin (1 + ((1 + n) + (1 + n)))
adapt⤪ n =
                             fork×⤪ {1}     |⤪    id {A = Fin ((1 + n) + (1 + n))}
    ⟫⤪                   id {A = Fin 2}     |⤪    intertwine⤪ {1} {n} {1} {n}
    ⟫⤪                            ARL⤪ {1 + 1} {1 + 1} {n + n}
    ⟫⤪        intertwine⤪ {1} {1} {1} {1}   |⤪    id
    ⟫⤪  (id {A = Fin 2} |⤪ swap⤪ {1} {1})   |⤪    id {A = Fin (n + n)}
    ⟫⤪               ARL⤪ {1 + 1} {1} {1}   |⤪    id
    ⟫⤪                            ALR⤪ {1 + 1 + 1} {1} {n + n}

adapt⤨ : ∀ n → 𝐂 (1 + ((1 + n) + (1 + n))) ((1 + 1 + 1) + (1 + (n + n)))
adapt⤨ = Plug ∘ adapt⤪
\end{code}

%<*muxN-core>
\AgdaTarget{muxN}
\begin{code}
muxN : ∀ n → 𝐂 (1 + (n + n)) n
muxN zero    = Nil
muxN (suc n) = adapt⤨ n  ⟫  mux ∥ muxN n
\end{code}
%</muxN-core>
