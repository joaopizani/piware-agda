\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Function using (const; _∘_; _$_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; replicate; foldr)
import Algebra as A
import Data.Nat.Properties as NP
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (+-comm)

open import PiWare.Circuit.Core Gt using (ℂ'; Nil; _⟫'_; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
\end{code}


-- Base case relies on the identity of _|'_:
-- ∀ c' : Nil |' c' ≡⟦⟧  c'  (where _≡⟦⟧_ means "have same simulation semantics")
%<*pars-core>
\begin{code}
pars' : ∀ {k i o} → Vec (ℂ' i o) k → ℂ' (k * i) (k * o)
pars' {_} {i} {o} = foldr (λ k → ℂ' (k * i) (k * o)) _|'_ Nil
\end{code}
%</pars-core>

%<*parsN-core>
\begin{code}
parsN' : ∀ {k i o} → ℂ' i o → ℂ' (k * i) (k * o)
parsN' {k} = pars' ∘ replicate {n = k}
\end{code}
%</parsN-core>


-- Base case relies on the identity of _⟫'_:
-- ∀ c' : pid' ⟫' c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have same simulation semantics")
%<*seqs-core>
\begin{code}
seqs' : ∀ {k io} → Vec (ℂ' io io) k → ℂ' io io
seqs' {_} {io} = foldr (const $ ℂ' io io) _⟫'_ pid'
\end{code}
%</seqs-core>

%<*seqsN-core>
\begin{code}
seqsN' : (k : ℕ) {io : ℕ} → ℂ' io io → ℂ' io io
seqsN' k = seqs' ∘ replicate {n = k}
\end{code}
%</seqsN-core>


%<*row-core>
row' : ∀ {k i o r} → ℂ' (i + r) (o + r) → ℂ' (r + (k * i)) ((k * o) + r)
row' {zero}   {i} {o} {r} _ rewrite +-comm r 0  = pid'
row' {suc k'} {i} {o} {r} c' = {!row' {k'} c'!}
%</row-core>
