\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates

module PiWare.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open Gates At Gt using (Gates#; ins; outs)
\end{code}


%<*pre-decls>
\begin{code}
data ℂ' : ℕ → ℕ → Set
comb' : {i o : ℕ} → ℂ' i o → Set
\end{code}
%</pre-decls>

%<*Circuit-core>
\begin{code}
data ℂ' where
    Nil        : ℂ' zero zero
    Gate       : (g# : Gates#) → ℂ' (ins g#) (outs g#)
    DelayLoop  : ∀ {i o l} (c : ℂ' (i + l) (o + l)) {p : comb' c} → ℂ' i o

    Plug   : ∀ {i o}          → (f : Fin o → Fin i) → ℂ' i o
    _⟫'_   : ∀ {i m o}        → ℂ' i m → ℂ' m o → ℂ' i o
    _|'_   : ∀ {i₁ o₁ i₂ o₂}  → ℂ' i₁ o₁ → ℂ' i₂ o₂ → ℂ' (i₁ + i₂) (o₁ + o₂)
    _|+'_  : ∀ {i₁ i₂ o}      → ℂ' i₁ o → ℂ' i₂ o → ℂ' (suc (i₁ ⊔ i₂)) o
\end{code}
%</Circuit-core>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}


%<*comb-core>
\begin{code}
comb' Nil           = ⊤
comb' (Gate _)      = ⊤
comb' (Plug _)      = ⊤
comb' (DelayLoop _) = ⊥
comb' (c₁ ⟫' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |+' c₂)   = comb' c₁ × comb' c₂
\end{code}
%</comb-core>

%<*lemma-comb-seq'>
\begin{code}
_comb⟫'_ : {i m o : ℕ} {c₁' : ℂ' i m} {c₂' : ℂ' m o}
         → comb' c₁' → comb' c₂' → comb' (c₁' ⟫' c₂')
_comb⟫'_ = _,_
\end{code}
%</lemma-comb-seq'>

%<*lemma-comb-par'>
\begin{code}
_comb|'_ : {i₁ o₁ i₂ o₂ : ℕ} {c₁' : ℂ' i₁ o₁} {c₂' : ℂ' i₂ o₂}
         → comb' c₁' → comb' c₂' → comb' (c₁' |' c₂')
_comb|'_ = _,_
\end{code}
%</lemma-comb-par'>

%<*lemma-comb-sum'>
\begin{code}
_comb|+'_ : {i₁ i₂ o : ℕ} {c₁' : ℂ' i₁ o} {c₂' : ℂ' i₂ o}
          → comb' c₁' → comb' c₂' → comb' (c₁' |+' c₂')
_comb|+'_ = _,_
\end{code}
%</lemma-comb-sum'>
