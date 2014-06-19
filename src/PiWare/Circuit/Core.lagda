\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates

module PiWare.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open Gates At Gt using (Gates#; ins; outs)
\end{code}


\begin{code}
data ℂ' : ℕ → ℕ → Set
comb' : {i o : ℕ} → ℂ' i o → Set
\end{code}

\begin{code}
data ℂ' where
    Gate : (g# : Gates#) → ℂ' (ins g#) (outs g#)
    DelayLoop : {i o l : ℕ} (c : ℂ' (i + l) (o + l)) {p : comb' c} → ℂ' i o

    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' i o
    _⟫'_ : {i m o : ℕ} → ℂ' i m → ℂ' m o → ℂ' i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' i₁ o₁ → ℂ' i₂ o₂ → ℂ' (i₁ + i₂) (o₁ + o₂)
    _|+'_ : {i₁ i₂ o : ℕ} → ℂ' i₁ o → ℂ' i₂ o → ℂ' (suc (i₁ ⊔ i₂)) o
\end{code}
    
\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}


\begin{code}
comb' (Gate _)      = ⊤
comb' (Plug _)      = ⊤
comb' (DelayLoop _) = ⊥
comb' (c₁ ⟫' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |+' c₂)   = comb' c₁ × comb' c₂
\end{code}
