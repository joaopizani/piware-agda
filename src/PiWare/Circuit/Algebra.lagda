\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Algebra {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)

open import PiWare.Circuit Gt using (ℂ; σ; Nil; Gate; Plug; DelayLoop; _⟫_; _∥_; _|+_)
open Gates At Gt using (|in|; |out|)
\end{code}


%<*combinator-types-parameterized>
\begin{code}
TyNil★ TyGate★ TyPlug★ Ty⟫★ Ty∥★ Ty|+★ : (ℕ → ℕ → Set) → Set
TyNil★  F = ∀ {n}                     → F n zero
TyGate★ F = ∀ g#                      → F (|in| g#) (|out| g#)
TyPlug★ F = ∀ {i o} → (Fin o → Fin i) → F i o
Ty⟫★    F = ∀ {i m o}       → F i m   → F m o   → F i o
Ty∥★    F = ∀ {i₁ o₁ i₂ o₂} → F i₁ o₁ → F i₂ o₂ → F (i₁ + i₂) (o₁ + o₂)
Ty|+★   F = ∀ {i₁ i₂ o}     → F i₁ o  → F i₂ o  → F (suc (i₁ ⊔ i₂)) o
\end{code}
%</combinator-types-parameterized>


\begin{code}
module _ {Cσₓ : ℕ → ℕ → Set} where
\end{code}
%<*Circuit-combinational-algebra-type>
\begin{code}
 record ℂσ★ : Set where
   field Nil★  : TyNil★ Cσₓ
         Gate★ : TyGate★ Cσₓ
         Plug★ : TyPlug★ Cσₓ
         _⟫★_  : Ty⟫★ Cσₓ
         _∥★_  : Ty∥★ Cσₓ
         _|+★_ : Ty|+★ Cσₓ
\end{code}
%</Circuit-combinational-algebra-type>

\begin{code}
 module _ (Aℓ : ℂσ★) where
  open ℂσ★ Aℓ
\end{code}
%<*Circuit-combinational-cata>
\begin{code}
  cataℂσ : ∀ {i o} → ℂ {σ} i o → Cσₓ i o
  cataℂσ Nil        = Nil★
  cataℂσ (Gate g)   = Gate★ g
  cataℂσ (Plug f)   = Plug★ f
  cataℂσ (c₁ ⟫ c₂)  = cataℂσ c₁ ⟫★  cataℂσ c₂
  cataℂσ (c₁ ∥ c₂)  = cataℂσ c₁ ∥★  cataℂσ c₂
  cataℂσ (c₁ |+ c₂) = cataℂσ c₁ |+★ cataℂσ c₂
\end{code}
%</Circuit-combinational-cata>


\begin{code}
module _ {Cσₓ : ℕ → ℕ → Set} {Cₓ : ℕ → ℕ → Set} where
\end{code}
%<*Circuit-algebra-type>
\begin{code}
 record ℂ★ : Set where
   field Nil★  : TyNil★ Cₓ
         Gate★ : TyGate★ Cₓ
         Plug★ : TyPlug★ Cₓ
         _⟫★_  : Ty⟫★ Cₓ
         _∥★_  : Ty∥★ Cₓ
         _|+★_ : Ty|+★ Cₓ
         DelayLoop★ : ∀ {i o l} → Cσₓ (i + l) (o + l) → Cₓ i o
\end{code}
%</Circuit-algebra-type>

\begin{code}
 module _ (Aℓσ : ℂσ★ {Cσₓ}) (Aℓ : ℂ★) where
  open ℂ★ Aℓ
\end{code}
%<*Circuit-cata>
\begin{code}
  cataℂ : ∀ {i o} → ℂ i o → Cₓ i o
  cataℂ Nil           = Nil★
  cataℂ (Gate g)      = Gate★ g
  cataℂ (Plug f)      = Plug★ f
  cataℂ (DelayLoop c) = DelayLoop★ (cataℂσ {Cσₓ} Aℓσ c)
  cataℂ (c₁ ⟫ c₂)     = cataℂ c₁ ⟫★ cataℂ c₂
  cataℂ (c₁ ∥ c₂)     = cataℂ c₁ ∥★ cataℂ c₂
  cataℂ (c₁ |+ c₂)    = cataℂ c₁ |+★ cataℂ c₂
\end{code}
%</Circuit-cata>
