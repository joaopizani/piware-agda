\begin{code}
module PiWare.Samples.AndNCore where

open import Data.Nat using (zero; suc)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Core BoolTrio using (ℂ'X; _⟫'_; _|'_)
open import PiWare.Plugs.Core BoolTrio using (id⤨')
open import PiWare.Samples.BoolTrioCombCore using (⊤ℂ'; ∧ℂ')
\end{code}


%<*andN-core>
\AgdaTarget{andN'}
\begin{code}
andN' : ∀ n → ℂ'X n 1
andN' zero    = ⊤ℂ'
andN' (suc n) = id⤨' {1} |' andN' n  ⟫'  ∧ℂ'
\end{code}
%</andN-core>
