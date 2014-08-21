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


%<*Circuit-core-pre>
\begin{code}
data ℂ' : ℕ → ℕ → Set
\end{code}
%</Circuit-core-pre>
%<*comb-core-pre>
\begin{code}
comb' : {i o : ℕ} → ℂ' i o → Set
\end{code}
%</comb-core-pre>

%<*Circuit-core-comb>
\begin{code}
data ℂ' where
    Nil  : ℂ' zero zero
    Gate : (g# : Gates#) → ℂ' (ins g#) (outs g#)
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ' i o
    _⟫'_ : {i m o : ℕ} → ℂ' i m → ℂ' m o → ℂ' i o
    _|'_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ' i₁ o₁ → ℂ' i₂ o₂ → ℂ' (i₁ + i₂) (o₁ + o₂)
    _|+'_ : {i₁ i₂ o : ℕ} → ℂ' i₁ o → ℂ' i₂ o → ℂ' (suc (i₁ ⊔ i₂)) o
\end{code}
%</Circuit-core-comb>
%<*Circuit-core-seq>
\begin{code}
    DelayLoop : {i o l : ℕ} (c : ℂ' (i + l) (o + l))
                {p : comb' c} → ℂ' i o
\end{code}
%</Circuit-core-seq>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}


%<*comb-core-gist>
\begin{code}
comb' Nil           = ⊤
comb' (Gate _)      = ⊤
comb' (Plug _)      = ⊤
comb' (DelayLoop _) = ⊥
comb' (c₁ ⟫' c₂)    = comb' c₁ × comb' c₂
\end{code}
%</comb-core-gist>
%<*comb-core-rest>
\begin{code}
comb' (c₁ |' c₂)    = comb' c₁ × comb' c₂
comb' (c₁ |+' c₂)   = comb' c₁ × comb' c₂
\end{code}
%</comb-core-rest>

%<*lemma-comb-seq'>
\begin{code}
_comb⟫'_ : {i m o : ℕ} {c₁' : ℂ' i m} {c₂' : ℂ' m o} → comb' c₁' → comb' c₂' → comb' (c₁' ⟫' c₂')
_comb⟫'_ = _,_
\end{code}
%</lemma-comb-seq'>

%<*lemma-comb-par'>
\begin{code}
_comb|'_ : {i₁ o₁ i₂ o₂ : ℕ} {c₁' : ℂ' i₁ o₁} {c₂' : ℂ' i₂ o₂} → comb' c₁' → comb' c₂' → comb' (c₁' |' c₂')
_comb|'_ = _,_
\end{code}
%</lemma-comb-par'>

%<*lemma-comb-sum'>
\begin{code}
_comb|+'_ : {i₁ i₂ o : ℕ} {c₁' : ℂ' i₁ o} {c₂' : ℂ' i₂ o} → comb' c₁' → comb' c₂' → comb' (c₁' |+' c₂')
_comb|+'_ = _,_
\end{code}
%</lemma-comb-sum'>
