\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit {At : Atomic} {Gt : Gates At} where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Vec.Extra using (VecNaturalT)

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
data ℂ : {𝐜 : IsComb} → Ix → Ix → Set
\end{code}
%</Circuit-predecl>

%<*Circuit-any>
\AgdaTarget{𝐂}
\begin{code}
𝐂 : Ix → Ix → Set
𝐂 i o = ∀ {𝐜} → ℂ {𝐜} i o
\end{code}
%</Circuit-any>

\begin{code}
infixl 4 _⟫_
infixr 5 _∥_
\end{code}

%<*Circuit>
\AgdaTarget{ℂ, Gate, DelayLoop, Plug, \_⟫\_, \_∥\_}
\begin{code}
data ℂ where
    Gate  : ∀ g              → 𝐂 (|in| g) (|out| g)
    Plug  : ∀ {i o} → i ⤪ o  → 𝐂 i o
    _⟫_ : ∀ {i m o 𝐜}        → ℂ {𝐜} i m   → ℂ {𝐜} m o   → ℂ {𝐜} i o
    _∥_ : ∀ {i₁ o₁ i₂ o₂ 𝐜}  → ℂ {𝐜} i₁ o₁ → ℂ {𝐜} i₂ o₂ → ℂ {𝐜} (i₁ + i₂) (o₁ + o₂)

    DelayLoop : ∀ {i o l} → ℂ {σ} (i + l) (o + l) → ℂ {ω} i o
\end{code}
%</Circuit>
