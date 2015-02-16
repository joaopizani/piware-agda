\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Fin using (Fin)
open import Data.String using (String)

open Gates At Gt using (Gates#; |in|; |out|)
\end{code}


%<*IsComb>
\AgdaTarget{IsComb, σ, ω}
\begin{code}
IsComb = Bool

pattern σ = true
pattern ω = false
\end{code}
%</IsComb>


%<*Circuit-core-predecl>
\begin{code}
data ℂ' : {p : IsComb} → ℕ → ℕ → Set
\end{code}
%</Circuit-core-predecl>

%<*Circuit-core-comb>
\AgdaTarget{ℂ'σ}
\begin{code}
ℂ'σ : ℕ → ℕ → Set
ℂ'σ = ℂ' {σ}
\end{code}
%</Circuit-core-comb>

%<*Circuit-core-seq>
\AgdaTarget{ℂ'ω}
\begin{code}
ℂ'ω : ℕ → ℕ → Set
ℂ'ω = ℂ' {ω}
\end{code}
%</Circuit-core-seq>

%<*Circuit-core>
\AgdaTarget{ℂ', Nil, Gate, DelayLoop, Plug, \_⟫'\_, \_|'\_, \_|+'\_, \_Named\_}
\begin{code}
data ℂ' where
    Nil   : ∀ {p} → ℂ' {p} zero zero
    Gate  : (g# : Gates#) → ℂ'σ (|in| g#) (|out| g#)
    Plug  : ∀ {i o} → (Fin o → Fin i) → ℂ'σ i o

    DelayLoop : ∀ {i o l} → ℂ'σ (i + l) (o + l) → ℂ'ω i o

    _⟫'_  : ∀ {i m o p₁ p₂}       → ℂ' {p₁} i m   → ℂ' {p₂} m o   → ℂ' {p₁ ∧ p₂} i o
    _|'_  : ∀ {i₁ o₁ i₂ o₂ p₁ p₂} → ℂ' {p₁} i₁ o₁ → ℂ' {p₂} i₂ o₂ → ℂ' {p₁ ∧ p₂} (i₁ + i₂) (o₁ + o₂)
    _|+'_ : ∀ {i₁ i₂ o p₁ p₂}     → ℂ' {p₁} i₁ o  → ℂ' {p₂} i₂ o  → ℂ' {p₁ ∧ p₂} (suc (i₁ ⊔ i₂)) o

    _Named_ : ∀ {i o p} → ℂ' {p} i o → String → ℂ' {p} i o
\end{code}
%</Circuit-core>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}
