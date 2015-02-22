\begin{code}
module PiWare.ProofSamples.AndN where

open import Data.Nat using (zero; suc)
open import Data.Bool using (true)
open import Data.Vec using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation BoolTrio using (⟦_⟧)
open import PiWare.Samples.AndN using (andN)
open import PiWare.ProofSamples.AndNCore using (proof-andN-core-alltrue)
\end{code}


%<*proof-andN-alltrue>
\AgdaTarget{proof-andN-alltrue}
\begin{code}
proof-andN-alltrue : ∀ n → ⟦ andN n ⟧ (replicate true) ≡ true
proof-andN-alltrue zero    = refl
proof-andN-alltrue (suc n) rewrite proof-andN-core-alltrue n = refl
\end{code}
%</proof-andN-alltrue>
