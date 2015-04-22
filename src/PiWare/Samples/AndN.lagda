\begin{code}
module PiWare.Samples.AndN where

open import Data.Nat.Base using (zero; suc)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit {Gt = BoolTrio} using (𝐂; _⟫_; _∥_)
open import PiWare.Plugs BoolTrio using (id⤨)
open import PiWare.Samples.BoolTrioComb using (⊤ℂ; ∧ℂ)
\end{code}


%<*andN>
\AgdaTarget{andN}
\begin{code}
andN : ∀ n → 𝐂 n 1
andN zero    = ⊤ℂ
andN (suc n) = id⤨ {1} ∥ andN n  ⟫  ∧ℂ
\end{code}
%</andN>
