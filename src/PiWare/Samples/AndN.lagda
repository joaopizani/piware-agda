\begin{code}
module PiWare.Samples.AndN where

open import Function using (id)
open import Data.Nat using (zero; suc)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑[_,_])
open import PiWare.Synthesizable.Bool using (⇓W⇑-B)

open import PiWare.Gates.BoolTrio using (BoolTrio; ⊤ℂ#; ∧ℂ#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'X; Gate; _|'_; _⟫'_)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ)
open import PiWare.Plugs.Core BoolTrio using (pid')
\end{code}


%<*andN-core>
\AgdaTarget{andN'}
\begin{code}
andN' : ∀ n → ℂ'X n 1
andN' zero    = Gate ⊤ℂ#
andN' (suc n) = pid' {1} |' andN' n  ⟫'  Gate ∧ℂ#
\end{code}
%</andN-core>

%<*andN>
\AgdaTarget{andN}
\begin{code}
andN : ∀ n → ℂX (Vec B n) B
andN k = Mkℂ ⦃ sα = ⇓W⇑[ id , id ] ⦄ (andN' k)
\end{code}
%</andN>
