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
adaptEqI : ∀ {i i′ o 𝐜} (≡ᵢ : i ≡ i′) → ℂ {𝐜} i o → ℂ {𝐜} i′ o
adaptEqI ≡ᵢ rewrite ≡ᵢ = id
\end{code}
%</adaptEqI>


%<*adaptEqO>
\AgdaTarget{adaptEqO}
\begin{code}
adaptEqO : ∀ {i o o′ 𝐜} (≡ₒ : o ≡ o′) → ℂ {𝐜} i o → ℂ {𝐜} i o′
adaptEqO ≡ₒ rewrite ≡ₒ = id
\end{code}
%</adaptEqO>


%<*adaptEqIO>
\AgdaTarget{adaptEqIO}
\begin{code}
adaptEqIO : ∀ {i i′ o o′ 𝐜} (≡ᵢ : i ≡ i′) (≡ₒ : o ≡ o′) → ℂ {𝐜} i o → ℂ {𝐜} i′ o′
adaptEqIO ≡ᵢ ≡ₒ = adaptEqO ≡ₒ ∘′ adaptEqI ≡ᵢ
\end{code}
%</adaptEqIO>



\begin{code}
infixl 4 _⟫[_]-impl_
\end{code}

%<*seq-het-impl>
\AgdaTarget{\_⟫[\_]-impl\_}
\begin{code}
_⟫[_]-impl_ : ∀ {i m₁ m₂ o 𝐜} (c₁ : ℂ {𝐜} i m₁) (eq : m₁ ≡ m₂) (c₂ : ℂ {𝐜} m₂ o) → ℂ {𝐜} i o
c₁ ⟫[ eq ]-impl c₂ = c₁ ⟫ adaptId⤨ eq ⟫ c₂
\end{code}
%</seq-het-impl>

\begin{code}
abstract
\end{code}
%<*seq-het>
\AgdaTarget{\_⟫[\_]\_}
\begin{code}
 _⟫[_]_ : ∀ {i m₁ m₂ o 𝐜} (c₁ : ℂ {𝐜} i m₁) (eq : m₁ ≡ m₂) (c₂ : ℂ {𝐜} m₂ o) → ℂ {𝐜} i o
 _⟫[_]_ = _⟫[_]-impl_
\end{code}
%</seq-het>

-- TODO: reveal only works with the combinational equality
\begin{code}
abstract
\end{code}
%<*seq-het-reveal>
\AgdaTarget{reveal-⟫[]}
\begin{code}
 reveal-⟫[] : ∀ {i m o} {c₁ : ℂ i m} {c₂ : ℂ m o} → (c₁ ⟫[ refl ] c₂) ≋ (c₁ ⟫[ refl ]-impl c₂)
 reveal-⟫[] = ≋-refl
\end{code}
%</seq-het-reveal>



%<*par-het-left-impl>
\AgdaTarget{[\_]\_[\_]∥-impl\_}
\begin{code}
[_]_[_]∥-impl_ : ∀ {i₁ i₁′ i₂ o₁ o₁′ o₂ 𝐜} (≡ᵢ : i₁ ≡ i₁′) (c₁ : ℂ {𝐜} i₁ o₁) (≡ₒ : o₁ ≡ o₁′) (c₂ : ℂ {𝐜} i₂ o₂) → ℂ {𝐜} (i₁′ + i₂) (o₁′ + o₂)
[ ≡ᵢ ] c₁ [ ≡ₒ ]∥-impl c₂ = adaptEqIO ≡ᵢ ≡ₒ c₁ ∥ c₂
\end{code}
%</par-het-left-impl>

\begin{code}
abstract
\end{code}
%<*par-het-left>
\AgdaTarget{[\_]\_[\_]∥\_}
\begin{code}
 [_]_[_]∥_ : ∀ {i₁ i₁′ i₂ o₁ o₁′ o₂ 𝐜} (≡ᵢ : i₁ ≡ i₁′) (c₁ : ℂ {𝐜} i₁ o₁) (≡ₒ : o₁ ≡ o₁′) (c₂ : ℂ {𝐜} i₂ o₂) → ℂ {𝐜} (i₁′ + i₂) (o₁′ + o₂)
 [_]_[_]∥_ = [_]_[_]∥-impl_
\end{code}
%</par-het-left>

-- TODO: reveal only works with the combinational equality
\begin{code}
abstract
\end{code}
%<*par-het-left-reveal>
\AgdaTarget{reveal-∥[]l}
\begin{code}
 reveal-∥[]l : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → ([ refl ] c₁ [ refl ]∥ c₂) ≋ ([ refl ] c₁ [ refl ]∥-impl c₂)
 reveal-∥[]l = ≋-refl
\end{code}
%</par-het-left-reveal>



%<*par-het-right-impl>
\AgdaTarget{\_∥-impl[\_]\_[\_]}
\begin{code}
_∥-impl[_]_[_] : ∀ {i₁ i₂ i₂′ o₁ o₂ o₂′ 𝐜} (c₁ : ℂ {𝐜} i₁ o₁) (≡ᵢ : i₂ ≡ i₂′) (c₂ : ℂ {𝐜} i₂ o₂) (≡ₒ : o₂ ≡ o₂′) → ℂ {𝐜} (i₁ + i₂′) (o₁ + o₂′)
c₁ ∥-impl[ ≡ᵢ ] c₂ [ ≡ₒ ] = c₁ ∥ adaptEqIO ≡ᵢ ≡ₒ c₂
\end{code}
%</par-het-right-impl>

\begin{code}
abstract
\end{code}
%<*par-het-right>
\AgdaTarget{\_∥[\_]\_[\_]}
\begin{code}
 _∥[_]_[_] : ∀ {i₁ i₂ i₂′ o₁ o₂ o₂′ 𝐜} (c₁ : ℂ {𝐜} i₁ o₁) (≡ᵢ : i₂ ≡ i₂′) (c₂ : ℂ {𝐜} i₂ o₂) (≡ₒ : o₂ ≡ o₂′) → ℂ {𝐜} (i₁ + i₂′) (o₁ + o₂′)
 _∥[_]_[_] = _∥-impl[_]_[_]
\end{code}
%</par-het-right>

-- TODO: reveal only works with the combinational equality
\begin{code}
abstract
\end{code}
%<*par-het-right-reveal>
\AgdaTarget{reveal-∥[]r}
\begin{code}
 reveal-∥[]r : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → (c₁ ∥[ refl ] c₂ [ refl ]) ≋ (c₁ ∥-impl[ refl ] c₂ [ refl ])
 reveal-∥[]r = ≋-refl
\end{code}
%</par-het-right-reveal>



%<*par-het-input-impl>
\AgdaTarget{[\_]\_∥-impl[\_]\_}
\begin{code}
[_]_∥-impl[_]_ : ∀ {i₁ i₁′ i₂ i₂′ o₁ o₂ 𝐜} (≡₁ : i₁ ≡ i₁′) (c₁ : ℂ {𝐜} i₁ o₁) (≡₂ : i₂ ≡ i₂′) (c₂ : ℂ {𝐜} i₂ o₂) → ℂ {𝐜} (i₁′ + i₂′) (o₁ + o₂)
[ ≡₁ ] c₁ ∥-impl[ ≡₂ ] c₂ = adaptEqI ≡₁ c₁ ∥ adaptEqI ≡₂ c₂ 
\end{code}
%</par-het-input-impl>

\begin{code}
abstract
\end{code}
%<*par-het-input>
\AgdaTarget{[\_]\_∥[\_]\_}
\begin{code}
 [_]_∥[_]_ : ∀ {i₁ i₁′ i₂ i₂′ o₁ o₂ 𝐜} (≡₁ : i₁ ≡ i₁′) (c₁ : ℂ {𝐜} i₁ o₁) (≡₂ : i₂ ≡ i₂′) (c₂ : ℂ {𝐜} i₂ o₂) → ℂ {𝐜} (i₁′ + i₂′) (o₁ + o₂)
 [_]_∥[_]_ = [_]_∥-impl[_]_
\end{code}
%</par-het-input>

-- TODO: reveal only works with the combinational equality
\begin{code}
abstract
\end{code}
%<*par-het-input-reveal>
\AgdaTarget{reveal-∥[]i}
\begin{code}
 reveal-∥[]i : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → ([ refl ] c₁ ∥[ refl ] c₂) ≋ ([ refl ] c₁ ∥-impl[ refl ] c₂)
 reveal-∥[]i = ≋-refl
\end{code}
%</par-het-input-reveal>



%<*par-het-output-impl>
\AgdaTarget{\_[\_]∥-impl\_[\_]}
\begin{code}
_[_]∥-impl_[_] : ∀ {i₁ i₂ o₁ o₁′ o₂ o₂′ 𝐜} (c₁ : ℂ {𝐜} i₁ o₁) (≡₁ : o₁ ≡ o₁′) (c₂ : ℂ {𝐜} i₂ o₂) (≡₂ : o₂ ≡ o₂′) → ℂ {𝐜} (i₁ + i₂) (o₁′ + o₂′)
c₁ [ ≡₁ ]∥-impl c₂ [ ≡₂ ] = adaptEqO ≡₁ c₁ ∥ adaptEqO ≡₂ c₂
\end{code}
%</par-het-output-impl>

\begin{code}
abstract
\end{code}
%<*par-het-output>
\AgdaTarget{\_[\_]∥\_[\_]}
\begin{code}
 _[_]∥_[_] : ∀ {i₁ i₂ o₁ o₁′ o₂ o₂′ 𝐜} (c₁ : ℂ {𝐜} i₁ o₁) (≡₁ : o₁ ≡ o₁′) (c₂ : ℂ {𝐜} i₂ o₂) (≡₂ : o₂ ≡ o₂′) → ℂ {𝐜} (i₁ + i₂) (o₁′ + o₂′)
 _[_]∥_[_] = _[_]∥-impl_[_]
\end{code}
%</par-het-output>

-- TODO: reveal only works with the combinational equality
\begin{code}
abstract
\end{code}
%<*par-het-output-reveal>
\AgdaTarget{reveal-∥[]o}
\begin{code}
 reveal-∥[]o : ∀ {i₁ i₂ o₁ o₂} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} → (c₁ [ refl ]∥ c₂ [ refl ]) ≋ (c₁ [ refl ]∥-impl c₂ [ refl ])
 reveal-∥[]o = ≋-refl
\end{code}
%</par-het-output-reveal>



-- Base case relies on the identity of _∥_:
-- ∀ c' : id⤨ ∥ c' ≋ c'  (where _≋_ means "have same simulation semantics")
%<*pars>
\AgdaTarget{pars}
\begin{code}
pars : ∀ {k i o 𝐜} (cs : Vec (ℂ {𝐜} i o) k) → ℂ {𝐜} (k * i) (k * o)
pars {k} {i} {o} {𝐜} = foldr (λ k → ℂ {𝐜} (k * i) (k * o)) _∥_ id⤨
\end{code}
%</pars>

%<*parsN>
\AgdaTarget{parsN}
\begin{code}
parsN : ∀ {k i o 𝐜} → ℂ {𝐜} i o → ℂ {𝐜} (k * i) (k * o)
parsN {k} = pars ∘′ replicate {n = k}
\end{code}
%</parsN>


-- Base case relies on the identity of _⟫_:
-- ∀ c' : pid' ⟫ c' ≡⟦⟧ c'  (where _≡⟦⟧_ means "have same simulation semantics")
-- TODO: Here we force all ℂs to have the same size, a better version would be with type-aligned sequences
%<*seqs>
\AgdaTarget{seqs}
\begin{code}
seqs : ∀ {n io 𝐜} → Vec (ℂ {𝐜} io io) n → ℂ {𝐜} io io
seqs {_} {io} {𝐜} = foldr (const $ ℂ {𝐜} io io) _⟫_ id⤨
\end{code}
%</seqs>


--TODO: write as fold? (fold over Vec↑⁼)
-- Yorick's _⟫[_]_
seqs′ : ∀ {n is os 𝐜} → Vec↑⁼ (ℂ {𝐜}) (suc n) is os → ℂ {𝐜} (head is) (last os)
seqs′ (c ◁⁼[ p ] ε⁼) = c
seqs′ (c₁ ◁⁼[ p₁ ] c₂ ◁⁼[ p₂ ] cs) = c₁ ⟫ seqs′ {!c₂ ◁⁼[ p₂ ] cs!}


%<*seqsN>
\AgdaTarget{seqsN}
\begin{code}
seqsN : ∀ k {io 𝐜} → ℂ {𝐜} io io → ℂ {𝐜} io io
seqsN k = seqs ∘′ replicate {n = k}
\end{code}
%</seqsN>


-- TODO
%<*row>
\AgdaTarget{row}
\begin{code}
row : ∀ {k a b c 𝐜} → ℂ {𝐜} (a + b) (c + a) → ℂ {𝐜} (a + (k * b)) ((k * c) + a)
row {zero}  {a} {b} {c} _ rewrite +-right-identity a = id⤨
row {suc k} {a} {b} {c} f = ⊥ where postulate ⊥ : _  -- id⤨ {c} ∥ row {k} {a} {b} {c} f
\end{code}
%</row>
