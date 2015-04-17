\begin{code}
module PiWare.ProofSamples.AndN.Typed where

open import Data.Nat.Base using (zero; suc)
open import Data.Bool.Base using (true)
open import Data.Vec using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation.Typed BoolTrio using (⟦_⟧̂)
open import PiWare.Samples.AndN.Typed using (andN̂)
open import PiWare.ProofSamples.AndN using (proof-andN-alltrue)
\end{code}


%<*proof-andN-alltrue-typed>
\AgdaTarget{proof-andN-alltruê}
\begin{code}
proof-andN-alltruê : ∀ n → ⟦ andN̂ n ⟧̂ (replicate true) ≡ true
proof-andN-alltruê zero    = refl
proof-andN-alltruê (suc n) rewrite proof-andN-alltrue n = refl
\end{code}
%</proof-andN-alltrue-typed>
