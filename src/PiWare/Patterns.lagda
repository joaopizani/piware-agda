\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns {At : Atomic} (Gt : Gates At) where

open import Function using (const; _∘′_; _$_; id)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; replicate; foldr; head; last)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--open import Data.RVec using (Vec↑⁼; ε⁼; _◁⁼[_]_)

open import PiWare.Interface using (Ix)
open import PiWare.Circuit {Gt = Gt} using (ℂ; _⟫_; _∥_)
open import PiWare.Plugs Gt using (id⤨; adaptId⤨)
open import PiWare.Simulation.Equality Gt using (_≋_; ≋-refl)
\end{code}


%<*adaptEqI>
\AgdaTarget{adaptEqI}
\begin{code}
adaptEqI : ∀ {i i′ o p} (i≡ : i ≡ i′) → ℂ {p} i o → ℂ {p} i′ o
adaptEqI i≡ rewrite i≡ = id
\end{code}
%</adaptEqI>


%<*adaptEqO>
\AgdaTarget{adaptEqO}
\begin{code}
adaptEqO : ∀ {i o o′ p} (o≡ : o ≡ o′) → ℂ {p} i o → ℂ {p} i o′
adaptEqO o≡ rewrite o≡ = id
\end{code}
%</adaptEqO>


%<*adaptEqIO>
\AgdaTarget{adaptEqIO}
\begin{code}
adaptEqIO : ∀ {i i′ o o′ p} (i≡ : i ≡ i′) (o≡ : o ≡ o′) → ℂ {p} i o → ℂ {p} i′ o′
adaptEqIO i≡ o≡ = adaptEqO o≡ ∘′ adaptEqI i≡
\end{code}
%</adaptEqIO>



\begin{code}
infixl 4 _⟫[_]-impl_
\end{code}

%<*seq-het-impl>
\AgdaTarget{\_⟫[\_]-impl\_}
\begin{code}
_⟫[_]-impl_ : ∀ {i m₁ m₂ o p} (c₁ : ℂ {p} i m₁) (eq : m₁ ≡ m₂) (c₂ : ℂ {p} m₂ o) → ℂ {p} i o
c₁ ⟫[ eq ]-impl c₂ = c₁ ⟫ adaptId⤨ eq ⟫ c₂
\end{code}
%</seq-het-impl>

\begin{code}
abstract
\end{code}
%<*seq-het>
\AgdaTarget{\_⟫[\_]\_}
\begin{code}
 _⟫[_]_ : ∀ {i m₁ m₂ o p} (c₁ : ℂ {p} i m₁) (eq : m₁ ≡ m₂) (c₂ : ℂ {p} m₂ o) → ℂ {p} i o
 _⟫[_]_ = _⟫[_]-impl_
\end{code}
%</seq-het>

%<*seq-het-reveal>
\AgdaTarget{reveal-⟫[]}
\begin{code}
 reveal-⟫[] : ∀ {i m o} {c₁ : ℂ i m} {c₂ : ℂ m o} → (c₁ ⟫[ refl ] c₂) ≋ (c₁ ⟫[ refl ]-impl c₂)
 reveal-⟫[] = ≋-refl
\end{code}
%</seq-het-reveal>



\begin{code}
infixr 5 _∥[_]l[_]-impl_
\end{code}

%<*par-het-left-impl>
\AgdaTarget{\_∥[\_]l[\_]-impl\_}
\begin{code}
_∥[_]l[_]-impl_ : ∀ {i₁ i₁′ i₂ o₁ o₁′ o₂ p} (c₁ : ℂ {p} i₁ o₁) (i₁≡ : i₁ ≡ i₁′) (o₁≡ : o₁ ≡ o₁′) (c₂ : ℂ {p} i₂ o₂) → ℂ {p} (i₁′ + i₂) (o₁′ + o₂)
c₁ ∥[ i₁≡ ]l[ o₁≡ ]-impl c₂ = adaptEqIO i₁≡ o₁≡ c₁ ∥ c₂
\end{code}
%</par-het-left-impl>

\begin{code}
abstract
\end{code}
%<*par-het-left>
\AgdaTarget{\_∥[\_]l[\_]\_}
\begin{code}
 _∥[_]l[_]_ : ∀ {i₁ i₁′ i₂ o₁ o₁′ o₂ p} (c₁ : ℂ {p} i₁ o₁) (i₁≡ : i₁ ≡ i₁′) (o₁≡ : o₁ ≡ o₁′) (c₂ : ℂ {p} i₂ o₂) → ℂ {p} (i₁′ + i₂) (o₁′ + o₂)
 _∥[_]l[_]_ = _∥[_]l[_]-impl_
\end{code}
%</par-het-left>

%<*par-het-left-reveal>
\AgdaTarget{reveal-∥[]l}
\begin{code}
 reveal-∥[]l : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → (c₁ ∥[ refl ]l[ refl ] c₂) ≋ (c₁ ∥[ refl ]l[ refl ]-impl c₂)
 reveal-∥[]l = ≋-refl
\end{code}
%</par-het-left-reveal>



\begin{code}
infixr 5 _∥[_]r[_]-impl_
\end{code}

%<*par-het-right-impl>
\AgdaTarget{\_∥[\_]r[\_]-impl\_}
\begin{code}
_∥[_]r[_]-impl_ : ∀ {i₁ i₂ i₂′ o₁ o₂ o₂′ p} (c₁ : ℂ {p} i₁ o₁) (i₂≡ : i₂ ≡ i₂′) (o₂≡ : o₂ ≡ o₂′) (c₂ : ℂ {p} i₂ o₂) → ℂ {p} (i₁ + i₂′) (o₁ + o₂′)
c₁ ∥[ i₂≡ ]r[ o₂≡ ]-impl c₂ = c₁ ∥ adaptEqIO i₂≡ o₂≡ c₂
\end{code}
%</par-het-right-impl>

\begin{code}
abstract
\end{code}
%<*par-het-right>
\AgdaTarget{\_∥[\_]r[\_]\_}
\begin{code}
 _∥[_]r[_]_ : ∀ {i₁ i₂ i₂′ o₁ o₂ o₂′ p} (c₁ : ℂ {p} i₁ o₁) (i₂≡ : i₂ ≡ i₂′) (o₂≡ : o₂ ≡ o₂′) (c₂ : ℂ {p} i₂ o₂) → ℂ {p} (i₁ + i₂′) (o₁ + o₂′)
 _∥[_]r[_]_ = _∥[_]r[_]-impl_
\end{code}
%</par-het-right>

%<*par-het-right-reveal>
\AgdaTarget{reveal-∥[]r}
\begin{code}
 reveal-∥[]r : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → (c₁ ∥[ refl ]r[ refl ] c₂) ≋ (c₁ ∥[ refl ]r[ refl ]-impl c₂)
 reveal-∥[]r = ≋-refl
\end{code}
%</par-het-right-reveal>



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
