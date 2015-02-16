\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Fin using (Fin)
open import Data.Bool using (_∧_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-⊎)
import PiWare.Circuit.Core as CircuitCore
open CircuitCore Gt using (ℂ'; IsComb; Gate; Plug; DelayLoop; _⟫'_; _|'_; _|+'_; _Named_)
open CircuitCore Gt using (σ; ω) public

open Atomic At using (Atom#) 
open Gates At Gt using (|in|; |out|)
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

%<*Circuit-any>
\AgdaTarget{ℂX}
\begin{code}
ℂX : (α β : Set) {i j : ℕ} → Set
ℂX α β {i} {j} = ∀ {p} → ℂ {p} α β {i} {j}
\end{code}
%</Circuit-any>


-- "Smart constructors"
%<*gateC>
\AgdaTarget{gateℂ}
\begin{code}
gateℂ : ∀ g# {α β} ⦃ _ : ⇓W⇑ α {|in| g#} ⦄ ⦃ _ : ⇓W⇑ β {|out| g#} ⦄ → ℂX α β
gateℂ g# ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Gate g#)
\end{code}
%</gateC>

%<*plugC>
\AgdaTarget{plugℂ}
\begin{code}
plugℂ : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → (Fin j → Fin i) → ℂX α β {i} {j}
plugℂ ⦃ sα ⦄ ⦃ sβ ⦄ f = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Plug f)
\end{code}
%</plugC>

%<*named>
\AgdaTarget{\_named\_}
\begin{code}
_named_ : ∀ {α i β j p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂ {p} α β {i} {j} → String → ℂ {p} α β {i} {j}
_named_ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') s = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (c' Named s)
\end{code}
$</named>

%<*delayC>
\AgdaTarget{delayℂ}
\begin{code}
delayℂ : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
         → ℂ {σ} (α × γ) (β × γ) {i + k} {j + k} → ℂ {ω} α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c')
\end{code}
%</delayC>

%<*seq>
\AgdaTarget{\_⟫\_}
\begin{code}
_⟫_ : ∀ {α i β j γ k p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
      → ℂ {p} α β {i} {j} → ℂ {p} β γ {j} {k} → ℂ {p} α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ _ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)
\end{code}
%</seq>

%<*par>
\AgdaTarget{\_||\_}
\begin{code}
_||_ : ∀ {α i γ k β j δ l p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ δ {l} ⦄
       → ℂ {p} α γ {i} {k} → ℂ {p} β δ {j} {l} →  ℂ {p} (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ (c₁ |' c₂)
\end{code}
%</par>

%<*sum>
\AgdaTarget{|+}
\begin{code}
|+ : ∀ {α i β j γ k p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ (n m ε : Atom#) {d : n ≢ m}
     → ℂ {p} α γ {i} {k} → ℂ {p} β γ {j} {k} → ℂ {p} (α ⊎ β) γ {suc (i ⊔ j)} {k}
|+ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ n m ε {d} (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-⊎ n m ε {d} ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)
\end{code}
%</sum>

\begin{code}
infixr 9 _||_
infixl 8 _⟫_
\end{code}
