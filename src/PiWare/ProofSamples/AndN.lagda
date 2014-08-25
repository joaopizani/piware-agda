\begin{code}
module PiWare.ProofSamples.AndN where

open import Function using (_∘_)
open import Data.Nat using (zero; suc)
open import Data.Bool using (true)
open import Data.Vec using (replicate; [_]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Gates.BoolTrio using (BoolTrio; spec-and)
open import PiWare.Samples.AndN using (andN'; andN'-comb)
open import PiWare.Simulation.Core BoolTrio using (⟦_⟧')
\end{code}


%<*proof-andN-core-alltrue>
\begin{code}
proof-andN' : ∀ n → ⟦ andN' n ⟧' {andN'-comb n} (replicate true) ≡ [ true ]
proof-andN' zero     = refl
proof-andN' (suc n)  = cong  (spec-and ∘ (_∷_ true))
                             (proof-andN' n)
\end{code}
%</proof-andN-core-alltrue>
