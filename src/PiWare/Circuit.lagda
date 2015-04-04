\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)

open import PiWare.Interface using (Ix)
open import PiWare.Plugs.Core using (_⤪_)
open Gates At Gt using (|in|; |out|)
\end{code}


%<*IsComb>
\AgdaTarget{IsComb, σ, ω}
\begin{code}
data IsComb : Set where
  σ ω : IsComb  -- ω ≝ sequential
\end{code}
%</IsComb>

%<*Circuit-predecl>
\begin{code}
data ℂ : {p : IsComb} → Ix → Ix → Set
\end{code}
%</Circuit-predecl>

%<*Circuit-any>
\AgdaTarget{𝐂}
\begin{code}
𝐂 : Ix → Ix → Set
𝐂 i o = ∀ {p} → ℂ {p} i o
\end{code}
%</Circuit-any>

%<*Circuit>
\AgdaTarget{ℂ, Gate, DelayLoop, Plug, \_⟫\_, \_∥\_, \_|+\_}
\begin{code}
data ℂ where
    Gate  : ∀ g             → 𝐂 (|in| g) (|out| g)
    Plug  : ∀ {i o} → i ⤪ o → 𝐂 i o
    _⟫_ : ∀ {i m o p}       → ℂ {p} i m   → ℂ {p} m o   → ℂ {p} i o
    _∥_ : ∀ {i₁ o₁ i₂ o₂ p} → ℂ {p} i₁ o₁ → ℂ {p} i₂ o₂ → ℂ {p} (i₁ + i₂) (o₁ + o₂)

    DelayLoop : ∀ {i o l} → ℂ {σ} (i + l) (o + l) → ℂ {ω} i o
\end{code}
%</Circuit>

\begin{code}
infixl 4 _⟫_
infixr 5 _∥_
\end{code}
