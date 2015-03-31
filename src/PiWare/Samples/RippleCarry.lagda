\begin{code}
module PiWare.Samples.RippleCarry where

open import Function using (id; _$_)
open import Data.Nat using (zero; suc; _+_; _*_)
open import Data.Fin using (Fin)

open import PiWare.Plugs.Core using (_|⤪_; _⟫⤪_; id⤪; fst⤪; swap⤪; ARL⤪)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (𝐂; Plug; _⟫_; _∥_)
open import PiWare.Plugs BoolTrio using (id⤨; intertwine⤨; ALR⤨; ARL⤨; uncons⤨; cons⤨)
open import PiWare.Samples.BoolTrioComb using (fadd)
\end{code}


-- cin × a × b → s × cout
%<*ripple>
\AgdaTarget{ripple}
\begin{code}
ripple : ∀ n → 𝐂 (1 + (n * 1 + n * 1)) ((n * 1) + 1)
ripple zero    = Plug (id⤪ {1} |⤪ fst⤪ {0}  ⟫⤪  swap⤪ {1} {0})
ripple (suc m) =
     id⤨ {1}  ∥ (uncons⤨ {1} {m} ∥ uncons⤨ {1} {m}  ⟫  intertwine⤨ {1} {m * 1} {1} {m * 1})
  ⟫            assoc⤨
  ⟫        fadd  ∥  id⤨ {m * 1 + m * 1}
  ⟫        ALR⤨ {1} {1} {m * 1 + m * 1}
  ⟫     id⤨ {1}  ∥  ripple m
  ⟫       ARL⤨ {1} {m * 1} {1}
  where
    assoc⤨ = Plug $       ARL⤪ {1} {1 + 1} {m * 1 + m * 1}
                    ⟫⤪ ARL⤪ {1} {1} {1} |⤪ id⤪ {m * 1 + m * 1}
\end{code}
%</ripple>
