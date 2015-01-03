\begin{code}
module PiWare.Samples.AndN where

open import Function using (id)
open import Data.Nat using (zero; suc; _*_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using (Vec)

import Algebra as A
import Data.Nat.Properties as NP
open A.CommutativeSemiring NP.commutativeSemiring using (*-identity)
open import Relation.Binary.PropositionalEquality using (sym)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑[_,_])
open import PiWare.Synthesizable.Bool using ()  -- only instances

open import PiWare.Gates.BoolTrio using (BoolTrio; TrueConst#; And#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _|'_; _⟫'_; comb')
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; comb)
open import PiWare.Plugs.Core BoolTrio using (pid')
\end{code}


%<*andN-core>
\AgdaTarget{andN'}
\begin{code}
andN' : ∀ n → ℂ' n 1
andN' zero    = Gate TrueConst#
andN' (suc n) = pid' {1} |' andN' n  ⟫'  Gate And#
\end{code}
%</andN-core>

%<*andN-core-comb>
\AgdaTarget{andN'-comb}
\begin{code}
andN'-comb : ∀ n → comb' (andN' n)
andN'-comb zero    = tt
andN'-comb (suc n) = (tt , andN'-comb n) , tt
\end{code}
%</andN-core-comb>

%<*andN>
\AgdaTarget{andN}
\begin{code}
andN : ∀ n → ℂ (Vec B n) B {n} {1}
andN k = Mkℂ ⦃ sα = ⇓W⇑[ id , id ] ⦄ (andN' k)
\end{code}
%</andN>

%<*andN-comb>
\AgdaTarget{andN-comb}
\begin{code}
andN-comb : ∀ n → comb (andN n)
andN-comb = andN'-comb
\end{code}
%</andN-comb>
