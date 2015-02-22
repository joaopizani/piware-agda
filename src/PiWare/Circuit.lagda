\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)

open Gates At Gt using (Gates#; |in|; |out|)
\end{code}


%<*IsComb>
\AgdaTarget{IsComb, σ, ω}
\begin{code}
data IsComb : Set where σ ω : IsComb
\end{code}
%</IsComb>

%<*Circuit-predecl>
\begin{code}
data ℂ : {p : IsComb} → ℕ → ℕ → Set
\end{code}
%</Circuit-predecl>

%<*Circuit-any>
\AgdaTarget{𝐜}
\begin{code}
𝐂 : ℕ → ℕ → Set
𝐂 i o = ∀ {p} → ℂ {p} i o
\end{code}
%</Circuit-any>

%<*Circuit>
\AgdaTarget{ℂ, Nil, Gate, DelayLoop, Plug, \_⟫\_, \_∥\_, \_|+\_}
\begin{code}
data ℂ where
    Nil   : ∀ {n} → 𝐂 n zero
    Gate  : (g# : Gates#) → 𝐂 (|in| g#) (|out| g#)
    Plug  : ∀ {i o} → (Fin o → Fin i) → 𝐂 i o

    DelayLoop : ∀ {i o l} → ℂ {σ} (i + l) (o + l) → ℂ {ω} i o

    _⟫_  : ∀ {i m o p}       → ℂ {p} i m   → ℂ {p} m o   → ℂ {p} i o
    _∥_  : ∀ {i₁ o₁ i₂ o₂ p} → ℂ {p} i₁ o₁ → ℂ {p} i₂ o₂ → ℂ {p} (i₁ + i₂) (o₁ + o₂)
    _|+_ : ∀ {i₁ i₂ o p}     → ℂ {p} i₁ o  → ℂ {p} i₂ o  → ℂ {p} (suc (i₁ ⊔ i₂)) o
\end{code}
%</Circuit>

\begin{code}
infixl 4 _⟫_
infixr 5 _∥_
infixr 5 _|+_
\end{code}
