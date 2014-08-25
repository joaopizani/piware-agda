\begin{code}
module PiWare.Samples.AndN where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import PiWare.Gates.BoolTrio using (BoolTrio; TrueConst#; And#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _|'_; _⟫'_; comb')
open import PiWare.Plugs.Core BoolTrio using (pid')
\end{code}


<*andN-core-aux>
\begin{code}
⊤ℂ'   = Gate TrueConst#
∧ℂ'   = Gate And#
idℂ'  = pid' {1}
\end{code}
</andN-core-aux>
%<*andN-core>
\begin{code}
andN' : ∀ n → ℂ' n 1
andN' zero    = ⊤ℂ'
andN' (suc n) = idℂ' |' andN' n  ⟫'  ∧ℂ'
\end{code}
%</andN-core>

%<*andN-core-comb>
\begin{code}
andN'-comb : ∀ n → comb' (andN' n)
andN'-comb zero    = tt
andN'-comb (suc n) = (tt , andN'-comb n) , tt
\end{code}
%</andN-core-comb>
