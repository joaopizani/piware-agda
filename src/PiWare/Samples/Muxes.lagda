\begin{code}
module PiWare.Samples.Muxes where

open import Data.Nat using (_+_; _*_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; proj₂)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ)
open import PiWare.Samples.MuxesCore using (mux'; muxN')

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable.Bool using ()
open import PiWare.Synthesizable Atomic-B using (⇓W⇑)

import Algebra as A
import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (*-identity)
*-identity-right = proj₂ *-identity
\end{code}


%<*mux>
\AgdaTarget{mux}
\begin{code}
mux : ℂX (B × (B × B)) B
mux = Mkℂ mux'
\end{code}
%</mux>


\begin{code}
postulate muxN-sα : ∀ n → ⇓W⇑ (B × (Vec B n × Vec B n)) {1 + (n + n)}
postulate muxN-sβ : ∀ n → ⇓W⇑ (Vec B n) {n}
\end{code}

%<*muxN>
\AgdaTarget{muxN}
\begin{code}
muxN : ∀ n → ℂX (B × (Vec B n × Vec B n)) (Vec B n) {1 + ((n * 1) + (n * 1))} {n * 1}
muxN n rewrite *-identity-right n = Mkℂ ⦃ muxN-sα n ⦄ ⦃ muxN-sβ n ⦄ (muxN' n)
\end{code}
%</muxN>
