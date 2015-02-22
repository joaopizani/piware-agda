\begin{code}
module PiWare.ProofSamples.AndN where

open import Function using (_∘′_)
open import Data.Nat using (zero; suc)
open import Data.Bool using (true)
open import Data.Vec using (replicate; _∷_; [_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Gates.BoolTrio using (BoolTrio; spec-and)
open import PiWare.Simulation BoolTrio using (⟦_⟧)
open import PiWare.Samples.AndN using (andN)
\end{code}


%<*proof-andN-alltrue>
\AgdaTarget{proof-andN-alltrue}
\begin{code}
proof-andN-alltrue : ∀ n → ⟦ andN n ⟧ (replicate true) ≡ [ true ]
proof-andN-alltrue zero    = refl
proof-andN-alltrue (suc n) = cong (spec-and ∘′ _∷_ true) (proof-andN-alltrue n)
\end{code}
%</proof-andN-alltrue>
