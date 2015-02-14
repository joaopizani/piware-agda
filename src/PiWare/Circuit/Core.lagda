\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.String using (String)

open Gates At Gt using (Gates#; |in|; |out|)
\end{code}


%<*IsComb>
\begin{code}
IsComb : Set
IsComb = Bool

pattern σ = true
pattern ω = false
\end{code}
%</IsComb>


%<*Circuit-core-predecl>
\begin{code}
data ℂ' : {cs : IsComb} → ℕ → ℕ → Set
\end{code}
%</Circuit-core-predecl>


%<*AnyCircuit-core>
\begin{code}
Anyℂ' : ℕ → ℕ → Set
Anyℂ' i o = ∀ {p} → ℂ' {p} i o
\end{code}
%</AnyCircuit-core>


%<*Circuit-core>
\begin{code}
data ℂ' where
    Nil   : Anyℂ' zero zero
    Gate  : (g# : Gates#) → Anyℂ' (|in| g#) (|out| g#)
    DelayLoop : ∀ {i o l} (c : ℂ' {σ} (i + l) (o + l)) → ℂ' {ω} i o

    Plug : ∀ {i o} → (f : Fin o → Fin i) → Anyℂ' i o
    _⟫'_ : ∀ {i m o p} → ℂ' {p} i m → ℂ' {p} m o → ℂ' {p} i o
    _|'_ : ∀ {i₁ o₁ i₂ o₂ p} → ℂ' {p} i₁ o₁ → ℂ' {p} i₂ o₂ → ℂ' {p} (i₁ + i₂) (o₁ + o₂)
    _|+'_ : ∀ {i₁ i₂ o p} → ℂ' {p} i₁ o → ℂ' {p} i₂ o → ℂ' {p} (suc (i₁ ⊔ i₂)) o

    _Named_ : ∀ {i o p} → ℂ' {p} i o → String → ℂ' {p} i o
\end{code}
%</Circuit-core>

\begin{code}
infixr 5 _|'_
infixr 5 _|+'_
infixl 4 _⟫'_
\end{code}

