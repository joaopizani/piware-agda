\begin{code}
module PiWare.ProofSamples.AndNCore where

open import Function using (_∘′_)
open import Data.Nat using (zero; suc)
open import Data.Bool using (true)
open import Data.Vec using (replicate; _∷_; [_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Gates.BoolTrio using (BoolTrio; spec-and)
open import PiWare.Simulation.Core BoolTrio using (⟦_⟧')
open import PiWare.Samples.AndNCore using (andN')
\end{code}


%<*proof-andN-core-alltrue>
\AgdaTarget{proof-andN-core-alltrue}
\begin{code}
proof-andN-core-alltrue : ∀ n → ⟦ andN' n ⟧' (replicate true) ≡ [ true ]
proof-andN-core-alltrue zero    = refl
proof-andN-core-alltrue (suc n) = cong (spec-and ∘′ _∷_ true) (proof-andN-core-alltrue n)
\end{code}
%</proof-andN-core-alltrue>
