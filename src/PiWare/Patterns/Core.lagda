\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import Algebra as A
import Data.Nat.Properties as NP
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (+-comm)

open import PiWare.Circuit.Core Gt using (ℂ'; Nil; _⟫'_; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
\end{code}


Base case relies on the identity of _|'_:
∀ c' : Nil |' c' ≡⟦⟧  c'  (where _≡⟦⟧_ means "have the same simulation semantics")
%<*pars'>
\begin{code}
pars' : ∀ {k i o} → ℂ' i o → ℂ' (k * i) (k * o)
pars' {zero}  _  = Nil
pars' {suc k} c' = c' |' pars' {k} c'
\end{code}
%</pars'>


Base case relies on the identity of _⟫'_:
∀ c' : pid' ⟫' c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have the same simulation semantics")
%<*seqs'>
\begin{code}
seqs' : (k : ℕ) {io : ℕ} → ℂ' io io → ℂ' io io
seqs' zero     _  = pid'
seqs' (suc k') c' = c' ⟫' seqs' k' c'
\end{code}
%</seqs'>


%<*row'>
row' : ∀ {k i o r} → ℂ' (i + r) (o + r) → ℂ' (r + (k * i)) ((k * o) + r)
row' {zero}   {i} {o} {r} _ rewrite +-comm r 0  = pid'
row' {suc k'} {i} {o} {r} c' = {!row' {k'} c'!}
%</row'>
