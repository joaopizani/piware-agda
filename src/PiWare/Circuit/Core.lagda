\begin{code}
module PiWare.Circuit.Core where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open import PiWare.Atom using (AtomInfo)
\end{code}


\begin{code}
data ℂ' (AI : AtomInfo) : ℕ → ℕ → Set
comb' : ∀ {AI i o} → ℂ' AI i o → Set
\end{code}

\begin{code}
data ℂ' AI where
    -- Fundamental gates
    Not : ℂ' AI 1 1
    And : ℂ' AI 2 1
    Or  : ℂ' AI 2 1

    -- Introduce loop, make sequential
    DelayLoop : {i o l : ℕ} (c : ℂ' AI (i + l) (o + l)) {p : comb' c} → ℂ' AI i o

    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' AI i o
    _⟫'_ : {i m o : ℕ} → ℂ' AI i m → ℂ' AI m o → ℂ' AI i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' AI i₁ o₁ → ℂ' AI i₂ o₂ → ℂ' AI (i₁ + i₂) (o₁ + o₂)
    _|+'_ : {i₁ i₂ o : ℕ} → ℂ' AI i₁ o → ℂ' AI i₂ o → ℂ' AI (suc (i₁ ⊔ i₂)) o
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
