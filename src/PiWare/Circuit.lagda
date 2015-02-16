\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Bool using (_∧_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-⊎)
open import PiWare.Circuit.Core Gt using (ℂ'; IsComb; σ; ω; DelayLoop; _⟫'_; _|'_; _|+'_; _Named_)

open Atomic At using (Atom#) 
\end{code}


-- "High-level" circuit types, packing the synthesizable instances
%<*Circuit>
\AgdaTarget{ℂ}
\begin{code}
record ℂ {p : IsComb} (α β : Set) {i j : ℕ} : Set where
    inductive
    constructor Mkℂ
    field
        ⦃ sα ⦄ : ⇓W⇑ α {i}
        ⦃ sβ ⦄ : ⇓W⇑ β {j}
        base : ℂ' {p} i j

\end{code}
%</Circuit>

%<*Circuit-comb>
\begin{code}
ℂσ : (α β : Set) {i j : ℕ} → Set
ℂσ α β {i} {j} = ℂ {σ} α β {i} {j}
\end{code}
%</Circuit-comb>

%<*Circuit-seq>
\begin{code}
ℂω : (α β : Set) {i j : ℕ} → Set
ℂω α β {i} {j} = ℂ {ω} α β {i} {j}
\end{code}
%</Circuit-seq>


-- "Smart constructors"
%<*named>
\begin{code}
_named_ : ∀ {α i β j p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂ {p} α β {i} {j} → String → ℂ {p} α β {i} {j}
_named_ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') s = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (c' Named s)
\end{code}
$</named>

%<*delayC>
\begin{code}
delayℂ : ∀ {α i β j γ k} → ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
         → ℂσ (α × γ) (β × γ) {i + k} {j + k} → ℂω α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c')
\end{code}
%</delayC>

%<*seq>
\begin{code}
_⟫_ : ∀ {α i β j γ k p₁ p₂} → ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
      → ℂ {p₁} α β {i} {j} → ℂ {p₂} β γ {j} {k} → ℂ {p₁ ∧ p₂} α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ _ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)
\end{code}
%</seq>

%<*par>
\begin{code}
_||_ : ∀ {α i γ k β j δ l p₁ p₂} → ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ δ {l} ⦄
       → ℂ {p₁} α γ {i} {k} → ℂ {p₂} β δ {j} {l} →  ℂ {p₁ ∧ p₂} (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ (c₁ |' c₂)
\end{code}
%</par>

%<*sum>
\begin{code}
|+ : ∀ {α i β j γ k p₁ p₂} → ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ (n m ε : Atom#) {d : n ≢ m}
     → ℂ {p₁} α γ {i} {k} → ℂ {p₂} β γ {j} {k} → ℂ {p₁ ∧ p₂} (α ⊎ β) γ {suc (i ⊔ j)} {k}
|+ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ n m ε {d} (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-⊎ n m ε {d} ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)
\end{code}
%</sum>

\begin{code}
infixr 9 _||_
infixl 8 _⟫_
\end{code}
