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
open import Relation.Binary.PropositionalEquality using (sym)
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (*-identity)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑[_,_])
open import PiWare.Synthesizable.Bool using (⇓W⇑-B)

open import PiWare.Gates.BoolTrio using (BoolTrio; ⊤ℂ#; ∧ℂ#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Anyℂ'; Gate; _|'_; _⟫'_)
open import PiWare.Circuit BoolTrio using (ℂ; Anyℂ; Mkℂ)
open import PiWare.Plugs.Core BoolTrio using (pid')
\end{code}


%<*andN-core>
\begin{code}
andN' : ∀ n → Anyℂ' n 1
andN' zero    = Gate ⊤ℂ#
andN' (suc n) = pid' {1} |' andN' n  ⟫'  Gate ∧ℂ#
\end{code}
%</andN-core>

%<*andN>
\begin{code}
andN : ∀ n → Anyℂ (Vec B n) B {n} {1}
andN k = Mkℂ ⦃ sα = ⇓W⇑[ id , id ] ⦄ (andN' k)
\end{code}
%</andN>
