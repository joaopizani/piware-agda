\begin{code}
module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open import PiWare.Atom using (Atomic)
\end{code}


\begin{code}
data ℂ' (At : Atomic) : ℕ → ℕ → Set
comb' : ∀ {At i o} → ℂ' At i o → Set
\end{code}

\begin{code}
data ℂ' At where
    -- Fundamental gates
    Not : ℂ' At 1 1
    And : ℂ' At 2 1
    Or  : ℂ' At 2 1

    -- Introduce loop, make sequential
    DelayLoop : {i o l : ℕ} (c : ℂ' At (i + l) (o + l)) {p : comb' c} → ℂ' At i o

    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' At i o
    _⟫'_ : {i m o : ℕ} → ℂ' At i m → ℂ' At m o → ℂ' At i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' At i₁ o₁ → ℂ' At i₂ o₂ → ℂ' At (i₁ + i₂) (o₁ + o₂)
    _|+'_ : {i₁ i₂ o : ℕ} → ℂ' At i₁ o → ℂ' At i₂ o → ℂ' At (suc (i₁ ⊔ i₂)) o
\end{code}
    
\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}


\begin{code}
comb' Not           = ⊤
comb' And           = ⊤
comb' Or            = ⊤
comb' (Plug f)      = ⊤
comb' (DelayLoop c) = ⊥
comb' (c₁ ⟫' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |+' c₂)   = comb' c₁ × comb' c₂
\end{code}
