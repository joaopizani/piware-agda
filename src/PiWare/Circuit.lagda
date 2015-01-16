\begin{code}
open import PiWare.Atom
open import PiWare.Gates using (Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-⊎)
open import PiWare.Circuit.Core Gt using (CombSeq; Comb; Seq) public
open import PiWare.Circuit.Core Gt
     using (ℂ'; DelayLoop; _⟫'_; _|'_; _|+'_; _Named_)

open Atomic At using (Atom#) 
\end{code}


-- "High-level" circuit types, packing the synthesizable instances
%<*Circuit>
\begin{code}
record ℂ {cs : CombSeq} (α β : Set) {i j : ℕ} : Set where
    inductive
    constructor Mkℂ
    field
        ⦃ sα ⦄ : ⇓W⇑ α {i}
        ⦃ sβ ⦄ : ⇓W⇑ β {j}
        base   : ℂ' {cs} i j

\end{code}
%</Circuit>


-- "Smart constructors"
%<*named>
\begin{code}
_named_ : ∀ {cs α i β j} ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ {cs} α β {i} {j} → String → ℂ {cs} α β {i} {j}
_named_ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') s = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (c' Named s)
\end{code}
$</named>

%<*delayC>
\begin{code}
delayℂ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
         → (c : ℂ {Comb} (α × γ) (β × γ) {i + k} {j + k}) → ℂ α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c') = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c')
\end{code}
%</delayC>

%<*seq>
\begin{code}
_⟫_ : ∀ {cs α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
      → ℂ {cs} α β {i} {j} → ℂ {cs} β γ {j} {k} → ℂ {cs} α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)
\end{code}
%</seq>

%<*par>
\begin{code}
_||_ : ∀ {cs α i γ k β j δ l} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sδ : ⇓W⇑ δ {l} ⦄
       → ℂ {cs} α γ {i} {k} → ℂ {cs} β δ {j} {l} →  ℂ {cs} (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ (c₁ |' c₂)
\end{code}
%</par>

%<*sum>
\begin{code}
|+ : ∀ {cs α i β j γ k}
       → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
       → (n₁ n₂ p : Atom#) {diff : n₁ ≢ n₂}
       → ℂ {cs} α γ {i} {k} → ℂ {cs} β γ {j} {k} → ℂ {cs} (α ⊎ β) γ {suc (i ⊔ j)} {k}
|+ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ n₁ n₂ p {d} (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ ⦃ ⇓W⇑-⊎ n₁ n₂ p {d} ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)
\end{code}
%</sum>

\begin{code}
infixr 9 _||_
infixl 8 _⟫_
\end{code}

