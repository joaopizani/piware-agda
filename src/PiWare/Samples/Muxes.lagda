\begin{code}
module PiWare.Samples.Muxes where

open import Function using (_$_)
open import Data.Nat using (zero; suc; _+_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; proj₂)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using ()
open import PiWare.Synthesizable.Bool using ()
open import PiWare.Gates.BoolTrio using (BoolTrio; ¬ℂ#; ∧ℂ#; ∨ℂ#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'X; Nil; Gate; _⟫'_; _|'_)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ; nilℂ; _⟫_; _||_)
open import PiWare.Plugs.Core BoolTrio using (pid'; pFork'; pFst'; pSnd')
open import PiWare.Plugs BoolTrio using (pFork×; pid; pFst; pSnd)
open import PiWare.Samples.BoolTrioComb using (¬ℂ; ∧ℂ; ∨ℂ)

import Algebra as A
import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (*-identity)

*-identity-r = proj₂ *-identity
\end{code}


\begin{code}
¬ℂ' : ℂ'X 1 1
¬ℂ' = Gate ¬ℂ#

∧ℂ' ∨ℂ' : ℂ'X 2 1
∧ℂ' = Gate ∧ℂ#
∨ℂ' = Gate ∨ℂ#
\end{code}

%<*mux2to1-core>
\AgdaTarget{mux2to1'}
\begin{code}
mux2to1' : ℂ'X 3 1  -- s × (a × b) → c
mux2to1' =
       pFork' {2}
    ⟫' (¬ℂ' |' pFst' {1} {1} ⟫' ∧ℂ') |' (pid' {1} |' pSnd' {1} {1} ⟫' ∧ℂ')
    ⟫' ∨ℂ'
\end{code}
%</mux2to1-core>

%<*mux2to1>
\AgdaTarget{mux2To1}
\begin{code}
mux2to1 : ℂX (B × (B × B)) B
mux2to1 = Mkℂ mux2to1'
\end{code}
%</mux2to1>


%<*muxN-core>
\AgdaTarget{muxN'}
\begin{code}
muxN' : ∀ n → ℂ'X (suc (n + n)) n
muxN' zero = Nil
muxN' (suc n) = pAdapt' ⟫' mux2to1' |' muxN' n
    where pAdapt' = {!!}
\end{code}
%</muxN-core>

%<*muxN>
\AgdaTarget{muxN}
muxN : ∀ n → let W = Vec B  in  ℂX (B × (W n × W n)) (W n) {suc (n + n)} {n}
muxN zero    = nilℂ
muxN (suc n) = _⟫_ ⦃ {!!} ⦄ ⦃ {!!} ⦄ ⦃ {!!} ⦄ (_⟫_ ⦃ {!!} ⦄ ⦃ {!!} ⦄ ⦃ {!!} ⦄ pAdapt (_||_ ⦃ {!!} ⦄ ⦃ {!!} ⦄ ⦃ {!!} ⦄ ⦃ {!!} ⦄ mux (muxN n))) {!pCons!}
    where pAdapt : let W = Vec B in ℂX (B × (W (suc n) × W (suc n))) ((B × (B × B)) × (B × (W n × W n)))
          pAdapt = {!!}
%</muxN>
