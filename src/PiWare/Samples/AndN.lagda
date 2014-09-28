\begin{code}
module PiWare.Samples.AndN where

open import Data.Nat using (zero; suc; _*_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using (Vec)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑-Vec)
open import PiWare.Synthesizable.Bool using (⇓W⇑-B)

open import PiWare.Gates.BoolTrio using (BoolTrio; TrueConst#; And#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _|'_; _⟫'_; comb')
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; comb)
open import PiWare.Plugs.Core BoolTrio using (pid')
\end{code}


%<*andN-core>
\begin{code}
andN' : ∀ n → ℂ' n 1
andN' zero    = Gate TrueConst#
andN' (suc n) = pid' {1} |' andN' n  ⟫'  Gate And#
\end{code}
%</andN-core>

%<*andN-core-comb>
\begin{code}
andN'-comb : ∀ n → comb' (andN' n)
andN'-comb zero    = tt
andN'-comb (suc n) = (tt , andN'-comb n) , tt
\end{code}
%</andN-core-comb>

%<*andN>
\begin{code}
andN : ∀ n → ℂ (Vec B n) B
andN n = Mkℂ (andN' (n * 1))
\end{code}
%</andN>

%<*andN-comb>
\begin{code}
andN-comb : ∀ n → comb (andN n)
andN-comb n = andN'-comb (n * 1)
\end{code}
%</andN-comb>
