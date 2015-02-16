\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Function using (const; _∘_; _$_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Vec using (Vec; []; _∷_; replicate; foldr; map)
open import Data.Product using (proj₂)

import Algebra as A
import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (+-identity)

open import PiWare.Circuit.Core Gt using (ℂ'; IsComb; Nil; _⟫'_; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
\end{code}


-- Base case relies on the identity of _|'_:
-- ∀ c' : Nil |' c' ≡⟦⟧  c'  (where _≡⟦⟧_ means "have same simulation semantics")
-- TODO: CAN WE combine here one ℂω with a lot of ℂX
%<*pars-core>
\AgdaTarget{pars'}
\begin{code}
pars' : ∀ {k i o p} (cs : Vec (ℂ' {p} i o) k) → ℂ' {p} (k * i) (k * o)
pars' {k} {i} {o} {p} = foldr (λ k → ℂ' {p} (k * i) (k * o)) _|'_ Nil
\end{code}
%</pars-core>

%<*parsN-core>
\AgdaTarget{parsN'}
\begin{code}
parsN' : ∀ {k i o p} → ℂ' {p} i o → ℂ' {p} (k * i) (k * o)
parsN' {k} = pars' ∘ replicate {n = k}
\end{code}
%</parsN-core>


-- Base case relies on the identity of _⟫'_:
-- ∀ c' : pid' ⟫' c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have same simulation semantics")
-- TODO: Here we force all ℂs to have the same size, a better version would be with type-aligned sequences
%<*seqs-core>
\AgdaTarget{seqs'}
\begin{code}
seqs' : ∀ {k io p} → Vec (ℂ' {p} io io) k → ℂ' {p} io io
seqs' {_} {io} {p} = foldr (const $ ℂ' {p} io io) _⟫'_ pid'
\end{code}
%</seqs-core>

%<*seqsN-core>
\AgdaTarget{seqsN'}
\begin{code}
seqsN' : ∀ k {io p} → ℂ' {p} io io → ℂ' {p} io io
seqsN' k = seqs' ∘ replicate {n = k}
\end{code}
%</seqsN-core>


%<*row-core>
\AgdaTarget{row'}
\begin{code}
row' : ∀ {k i o h p} → ℂ' {p} (h + i) (o + h) → ℂ' {p} (h + (k * i)) ((k * o) + h)
row' {zero}  {i} {o} {h} _ rewrite (proj₂ +-identity) h = pid'
row' {suc k} {i} {o} {h} c' = {!row' {k} {i} {o} {h} c'!}
\end{code}
%</row-core>
