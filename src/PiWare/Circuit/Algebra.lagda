\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Algebra {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Fin using (Fin)

open import PiWare.Interface using (Ix)
open import PiWare.Circuit Gt using (ℂ; σ; Nil; Gate; Plug; DelayLoop; _⟫_; _∥_; _⑆_)
open Gates At Gt using (|in|; |out|)
\end{code}


%<*combinator-types-parameterized>
\begin{code}
TyNil★ TyGate★ TyPlug★ Ty⟫★ Ty∥★ Ty⑆★ : (Ix → Ix → Set) → Set
TyNil★  F = ∀ {n}                     → F n zero
TyGate★ F = ∀ g#                      → F (|in| g#) (|out| g#)
TyPlug★ F = ∀ {i o} → (Fin o → Fin i) → F i o
Ty⟫★    F = ∀ {i m o}       → F i m   → F m o   → F i o
Ty∥★    F = ∀ {i₁ o₁ i₂ o₂} → F i₁ o₁ → F i₂ o₂ → F (i₁ + i₂) (o₁ + o₂)
Ty⑆★    F = ∀ {i₁ i₂ o}     → F i₁ o  → F i₂ o  → F (suc (i₁ ⊔ i₂)) o
\end{code}
%</combinator-types-parameterized>


\begin{code}
module _ {Carrier : Ix → Ix → Set} where
\end{code}
%<*Circuit-combinational-algebra-type>
\begin{code}
 record ℂσ★ : Set where
   field Nil★  : TyNil★ Carrier
         Gate★ : TyGate★ Carrier
         Plug★ : TyPlug★ Carrier
         _⟫★_  : Ty⟫★ Carrier
         _∥★_  : Ty∥★ Carrier
         _⑆★_  : Ty⑆★ Carrier
\end{code}
%</Circuit-combinational-algebra-type>

\begin{code}
 module _ (Aℓ : ℂσ★) where
  open ℂσ★ Aℓ
\end{code}
%<*Circuit-combinational-cata>
\begin{code}
  cataℂσ : ∀ {i o} → ℂ {σ} i o → Carrier i o
  cataℂσ Nil       = Nil★
  cataℂσ (Gate g)  = Gate★ g
  cataℂσ (Plug f)  = Plug★ f
  cataℂσ (c₁ ⟫ c₂) = cataℂσ c₁ ⟫★  cataℂσ c₂
  cataℂσ (c₁ ∥ c₂) = cataℂσ c₁ ∥★  cataℂσ c₂
  cataℂσ (c₁ ⑆ c₂) = cataℂσ c₁ ⑆★ cataℂσ c₂
\end{code}
%</Circuit-combinational-cata>


\begin{code}
module _ {Carrierσ : Ix → Ix → Set} {Carrier : Ix → Ix → Set} where
\end{code}
%<*Circuit-algebra-type>
\begin{code}
 record ℂ★ : Set where
   field Nil★  : TyNil★ Carrier
         Gate★ : TyGate★ Carrier
         Plug★ : TyPlug★ Carrier
         _⟫★_  : Ty⟫★ Carrier
         _∥★_  : Ty∥★ Carrier
         _⑆★_  : Ty⑆★ Carrier
         DelayLoop★ : ∀ {i o l} → Carrierσ (i + l) (o + l) → Carrier i o
\end{code}
%</Circuit-algebra-type>

\begin{code}
 module _ (Aℓσ : ℂσ★ {Carrierσ}) (Aℓ : ℂ★) where
  open ℂ★ Aℓ
\end{code}
%<*Circuit-cata>
\begin{code}
  cataℂ : ∀ {i o} → ℂ i o → Carrier i o
  cataℂ Nil           = Nil★
  cataℂ (Gate g)      = Gate★ g
  cataℂ (Plug f)      = Plug★ f
  cataℂ (DelayLoop c) = DelayLoop★ (cataℂσ {Carrierσ} Aℓσ c)
  cataℂ (c₁ ⟫ c₂)     = cataℂ c₁ ⟫★ cataℂ c₂
  cataℂ (c₁ ∥ c₂)     = cataℂ c₁ ∥★ cataℂ c₂
  cataℂ (c₁ ⑆ c₂)     = cataℂ c₁ ⑆★ cataℂ c₂
\end{code}
%</Circuit-cata>