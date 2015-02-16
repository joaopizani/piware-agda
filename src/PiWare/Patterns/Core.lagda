\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Function using (const; _∘_; _$_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Vec using (Vec; []; _∷_; replicate; foldr; map)
open import Data.Product using (Σ-syntax; proj₁)

import Algebra as A
import Data.Nat.Properties as NP
open A.CommutativeSemiring NP.commutativeSemiring using (+-comm)

open import PiWare.Circuit.Core Gt using (ℂ'; IsComb; Nil; _⟫'_; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
\end{code}


-- Base case relies on the identity of _|'_:
-- ∀ c' : Nil |' c' ≡⟦⟧  c'  (where _≡⟦⟧_ means "have same simulation semantics")
\begin{code}
and : ∀ {n} → Vec Bool n → Bool
and = foldr (const Bool) _∧_ true
\end{code}

%<*pars-core>
\AgdaTarget{pars'}
\begin{code}
pars' : ∀ {k i o} (cs : Vec (Σ[ p ∈ IsComb ] ℂ' {p} i o) k) → ℂ' {and (map proj₁ cs)} (k * i) (k * o)
pars' {k} {i} {o} = {!!}  -- foldr (λ k → ℂ' (k * i) (k * o)) _|'_ Nil
\end{code}
%</pars-core>

%<*parsN-core>
\AgdaTarget{parsN'}
parsN' : ∀ {k i o p} → ℂ' {p} i o → ℂ' {p} (k * i) (k * o)
parsN' {k} = pars' ∘ replicate {n = k}
%</parsN-core>


-- Base case relies on the identity of _⟫'_:
-- ∀ c' : pid' ⟫' c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have same simulation semantics")
%<*seqs-core>
\AgdaTarget{seqs'}
seqs' : ∀ {k io p} → Vec (ℂ' {p} io io) k → ℂ' {p} io io
seqs' {_} {io} = foldr (const $ ℂ' io io) _⟫'_ pid'
%</seqs-core>

%<*seqsN-core>
\AgdaTarget{seqsN'}
seqsN' : (k : ℕ) → ∀ {io p} → ℂ' {p} io io → ℂ' {p} io io
seqsN' k = seqs' ∘ replicate {n = k}
%</seqsN-core>


%<*row-core>
\AgdaTarget{row'}
row' : ∀ {k i o r} → ℂ' (i + r) (o + r) → ℂ' (r + (k * i)) ((k * o) + r)
row' {zero}   {i} {o} {r} _ rewrite +-comm r 0  = pid'
row' {suc k'} {i} {o} {r} c' = {!row' {k'} c'!}
%</row-core>
