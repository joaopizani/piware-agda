\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (zero; suc; _+_; _*_)
import Algebra as A
import Data.Nat.Properties as NP
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (+-comm)

open import PiWare.Circuit.Core Gt using (ℂ'; Nil; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
\end{code}


%<*pars'>
\begin{code}
pars' : ∀ {k i o} → ℂ' i o → ℂ' (k * i) (k * o)
pars' {zero}  _  = Nil
pars' {suc k} c' = c' |' pars' {k} c'
\end{code}
%</pars'>


%<*row'>
row' : ∀ {k i o r} → ℂ' (i + r) (o + r) → ℂ' (r + (k * i)) ((k * o) + r)
row' {zero}   {i} {o} {r} _ rewrite +-comm r 0  = pid'
row' {suc k'} {i} {o} {r} c' = {!row' {k'} c'!}
%</row'>
