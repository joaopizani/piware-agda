\begin{code}
module PiWare.Samples.RippleCarryCore where

open import Function using (id)
open import Data.Nat using (zero; suc; _+_; _*_)
open import Data.Fin using (Fin)

open import PiWare.Plugs.Functions using (_|⤪_; _⟫⤪_; fst⤪; swap⤪; ARL⤪)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Core BoolTrio using (ℂ'X; Plug; _⟫'_; _|'_)
open import PiWare.Plugs.Core BoolTrio using (id⤨'; intertwine⤨'; ALR⤨'; ARL⤨'; uncons⤨'; cons⤨')

open import PiWare.Samples.BoolTrioCombCore using (fadd')
\end{code}


-- cin × a × b → s × cout
%<*ripple-core>
\AgdaTarget{ripple'}
\begin{code}
ripple' : ∀ n → ℂ'X (1 + (n * 1 + n * 1)) ((n * 1) + 1)
ripple' zero    = Plug (id {A = Fin 1} |⤪ fst⤪ {0}  ⟫⤪  swap⤪ {1} {0})
ripple' (suc m) =
        id⤨' {1}  |' (uncons⤨' {1} {m} |' uncons⤨' {1} {m}  ⟫'  intertwine⤨' {1} {m * 1} {1} {m * 1})
    ⟫'      assoc⤨'
    ⟫'  fadd'  |'  id⤨' {m * 1 + m * 1}
    ⟫'       ALR⤨' {1} {1} {m * 1 + m * 1}
    ⟫'   id⤨' {1}  |'  ripple' m
    ⟫'       ARL⤨' {1} {m * 1} {1}
    where assoc⤨' = Plug (ARL⤪ {1} {1 + 1} {m * 1 + m * 1}  ⟫⤪  ARL⤪ {1} {1} {1} |⤪ id {A = Fin (m * 1 + m * 1)})
\end{code}
%</ripple-core>
