\begin{code}
module PiWare.Samples.Muxes where

open import Function using (_$_; _∘_; id)
open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc; _+_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)
open import Data.Product using (_×_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio; ¬ℂ#; ∧ℂ#; ∨ℂ#)
open import PiWare.Circuit.Core BoolTrio using (IsComb; ℂ'; ℂ'X; Nil; Gate; Plug; _⟫'_; _|'_)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ)
open import PiWare.Plugs.Functions using (fork×⤪; fst⤪; snd⤪; intertwine⤪; ALR⤪; ARL⤪; swap⤪; _⟫⤪_; _|⤪_)
open import PiWare.Plugs.Core BoolTrio using (id⤨'; fork×⤨'; fst⤨'; snd⤨')
\end{code}


\begin{code}
¬ℂ' : ℂ'X 1 1
¬ℂ' = Gate ¬ℂ#

∧ℂ' ∨ℂ' : ℂ'X 2 1
∧ℂ' = Gate ∧ℂ#
∨ℂ' = Gate ∨ℂ#
\end{code}

%<*mux-core>
\AgdaTarget{mux'}
\begin{code}
mux' : ℂ'X 3 1  -- s × (a × b) → c
mux' =
                                    fork×⤨'
    ⟫' (¬ℂ' |' fst⤨' {1} {1} ⟫' ∧ℂ')  |'  (id⤨' {1} |' snd⤨' {1} ⟫' ∧ℂ')
    ⟫'                                ∨ℂ'
\end{code}
%</mux-core>

%<*mux>
\AgdaTarget{mux}
\begin{code}
mux : ℂX (B × (B × B)) B
mux = Mkℂ mux'
\end{code}
%</mux>


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

adapt⤨' : ∀ n → ℂ'X (1 + ((1 + n) + (1 + n))) ((1 + 1 + 1) + (1 + (n + n)))
adapt⤨' = Plug ∘ adapt⤪
\end{code}

%<*muxN-core>
\AgdaTarget{muxN'}
\begin{code}
muxN' : ∀ n → ℂ'X (1 + (n + n)) n
muxN' zero    = Nil
muxN' (suc n) = adapt⤨' n  ⟫'  mux' |' muxN' n
\end{code}
%</muxN-core>


TODO: fix this (maybe there is a confusion between IsComb and Bool
\begin{code}
postulate muxN-sα : ∀ n → ⇓W⇑ (IsComb × Vec IsComb n × Vec IsComb n) {1 + (n + n)}
postulate muxN-sβ : ∀ n → ⇓W⇑ (Vec IsComb n) {n}
\end{code}

%<*muxN>
\AgdaTarget{muxN}
\begin{code}
muxN : ∀ n → ℂX (B × (Vec B n × Vec B n)) (Vec B n) {1 + (n + n)} {n}
muxN n = Mkℂ ⦃ muxN-sα n ⦄ ⦃ muxN-sβ n ⦄ (muxN' n)
\end{code}
%</muxN>
