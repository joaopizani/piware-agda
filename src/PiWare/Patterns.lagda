\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns {At : Atomic} (Gt : Gates At) where

open import Function using (const; _∘′_; _$_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; replicate; foldr; head; last)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Maybe.Base using (maybe′)

open import Data.RVec using (Vec↑⁼; ε⁼; _◁⁼[_]_)

open import PiWare.Interface using (Ix)
open import PiWare.Circuit {Gt = Gt} using (ℂ; _⟫_; _∥_)
open import PiWare.Plugs Gt using (id⤨)
\end{code}


-- Base case relies on the identity of _∥_:
-- ∀ c' : id⤨ ∥ c' ≋ c'  (where _≋_ means "have same simulation semantics")
%<*pars>
\AgdaTarget{pars}
\begin{code}
pars : ∀ {k i o p} (cs : Vec (ℂ {p} i o) k) → ℂ {p} (k * i) (k * o)
pars {k} {i} {o} {p} = foldr (λ k → ℂ {p} (k * i) (k * o)) _∥_ id⤨
\end{code}
%</pars>

%<*parsN>
\AgdaTarget{parsN}
\begin{code}
parsN : ∀ {k i o p} → ℂ {p} i o → ℂ {p} (k * i) (k * o)
parsN {k} = pars ∘′ replicate {n = k}
\end{code}
%</parsN>


-- Base case relies on the identity of _⟫_:
-- ∀ c' : pid' ⟫ c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have same simulation semantics")
-- TODO: Here we force all ℂs to have the same size, a better version would be with type-aligned sequences
%<*seqs>
\AgdaTarget{seqs}
\begin{code}
seqs : ∀ {n io p} → Vec (ℂ {p} io io) n → ℂ {p} io io
seqs {_} {io} {p} = foldr (const $ ℂ {p} io io) _⟫_ id⤨
\end{code}
%</seqs>


--TODO: write as fold? (fold over Vec↑⁼)
-- Yorick's _⟫[_]_
seqs′ : ∀ {n is os p} → Vec↑⁼ (ℂ {p}) (suc n) is os → ℂ {p} (head is) (last os)
seqs′ (c ◁⁼[ p ] ε⁼) = c
seqs′ (c₁ ◁⁼[ p₁ ] c₂ ◁⁼[ p₂ ] cs) = c₁ ⟫ seqs′ {!c₂ ◁⁼[ p₂ ] cs!}


%<*seqsN>
\AgdaTarget{seqsN}
\begin{code}
seqsN : ∀ k {io p} → ℂ {p} io io → ℂ {p} io io
seqsN k = seqs ∘′ replicate {n = k}
\end{code}
%</seqsN>


-- TODO
%<*row>
\AgdaTarget{row}
\begin{code}
row : ∀ {k a b c p} → ℂ {p} (a + b) (c + a) → ℂ {p} (a + (k * b)) ((k * c) + a)
row {zero}  {a} {b} {c} _ rewrite +-right-identity a = id⤨
row {suc k} {a} {b} {c} f = ⊥ where postulate ⊥ : _  -- id⤨ {c} ∥ row {k} {a} {b} {c} f
\end{code}
%</row>
