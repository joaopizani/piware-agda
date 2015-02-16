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

%<*Circuit-core-any>
\AgdaTarget{ℂ'X}
\begin{code}
ℂ'X : ℕ → ℕ → Set
ℂ'X i o = ∀ {p} → ℂ' {p} i o
\end{code}
%</Circuit-core-any>

%<*Circuit-core>
\AgdaTarget{ℂ', Nil, Gate, DelayLoop, Plug, \_⟫'\_, \_|'\_, \_|+'\_, \_Named\_}
\begin{code}
data ℂ' where
    Nil   : ℂ'X zero zero
    Gate  : (g# : Gates#) → ℂ'X (|in| g#) (|out| g#)
    Plug  : ∀ {i o} → (Fin o → Fin i) → ℂ'X i o

    DelayLoop : ∀ {i o l} → ℂ' {σ} (i + l) (o + l) → ℂ' {ω} i o

    _⟫'_  : ∀ {i m o p}       → ℂ' {p} i m   → ℂ' {p} m o   → ℂ' {p} i o
    _|'_  : ∀ {i₁ o₁ i₂ o₂ p} → ℂ' {p} i₁ o₁ → ℂ' {p} i₂ o₂ → ℂ' {p} (i₁ + i₂) (o₁ + o₂)
    _|+'_ : ∀ {i₁ i₂ o p}     → ℂ' {p} i₁ o  → ℂ' {p} i₂ o  → ℂ' {p} (suc (i₁ ⊔ i₂)) o

    _Named_ : ∀ {i o p} → ℂ' {p} i o → String → ℂ' {p} i o
\end{code}
%</Circuit-core>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}
