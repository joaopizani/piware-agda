\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.String using (String)

open Gates At Gt using (Gates#; |in|; |out|)
\end{code}


%<*CombSeq>
\begin{code}
data CombSeq : Set where
  Comb : CombSeq
  Seq : CombSeq
\end{code}
%</CombSeq>


%<*Circuit-core-predecl>
\begin{code}
data ℂ' : {cs : CombSeq} → ℕ → ℕ → Set
\end{code}
%</Circuit-core-predecl>


%<*AnyCircuit-core>
\begin{code}
Anyℂ' : ℕ → ℕ → Set
Anyℂ' i o = ∀ {cs} → ℂ' {cs} i o
\end{code}
%</AnyCircuit-core>


%<*Circuit-core>
\begin{code}
data ℂ' where
    Nil   : Anyℂ' zero zero
    Gate  : (g# : Gates#) → Anyℂ' (|in| g#) (|out| g#)
    DelayLoop : ∀ {i o l} (c : ℂ' {Comb} (i + l) (o + l)) → ℂ' {Seq} i o

    Plug : ∀ {i o} → (f : Fin o → Fin i) → Anyℂ' i o
    _⟫'_ : ∀ {i m o cs} → ℂ' {cs} i m → ℂ' {cs} m o → ℂ' {cs} i o
    _|'_ : ∀ {i₁ o₁ i₂ o₂ cs} → ℂ' {cs} i₁ o₁ → ℂ' {cs} i₂ o₂ → ℂ' {cs} (i₁ + i₂) (o₁ + o₂)
    _|+'_ : ∀ {i₁ i₂ o cs} → ℂ' {cs} i₁ o → ℂ' {cs} i₂ o → ℂ' {cs} (suc (i₁ ⊔ i₂)) o

    _Named_ : ∀ {i o cs} → ℂ' {cs} i o → String → ℂ' {cs} i o
\end{code}
%</Circuit-core>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}

