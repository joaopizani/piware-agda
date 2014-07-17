\begin{code}
open import PiWare.Atom
open import PiWare.Gates using (Gates)

module PiWare.Circuit {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-⊎)
open import PiWare.Circuit.Core Gt
     using (ℂ'; comb'; DelayLoop; _⟫'_; _|'_; _|+'_; _comb⟫'_; _comb|'_; _comb|+'_)

open Atomic At using (Atom#) 
\end{code}


-- "High-level" circuit types, packing the synthesizable instances
%<*Circuit>
\begin{code}
data ℂ (α β : Set) {i j : ℕ} : Set where
    Mkℂ : ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ' i j → ℂ α β {i} {j}
\end{code}
%</Circuit>


%<*comb>
\begin{code}
comb : ∀ {α i β j} → ℂ α β {i} {j} → Set
comb (Mkℂ c') = comb' c'
\end{code}
%</comb>


-- "Smart constructors"
%<*delayC>
\begin{code}
delayℂ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
         → (c : ℂ (α × γ) (β × γ) {i + k} {j + k}) {p : comb c} → ℂ α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c') {p} = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c' {p})
\end{code}
%</delayC>

%<*seq>
\begin{code}
_⟫_ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
      → ℂ α β {i} {j} → ℂ β γ {j} {k} → ℂ α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)
\end{code}
%</seq>

%<*par>
\begin{code}
_||_ : ∀ {α i γ k β j δ l} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sδ : ⇓W⇑ δ {l} ⦄
       → ℂ α γ {i} {k} → ℂ β δ {j} {l} →  ℂ (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-× sα sβ ⦄ ⦃ ⇓W⇑-× sγ sδ ⦄ (c₁ |' c₂)
\end{code}
%</par>

%<*sum>
\begin{code}
|+ : ∀ {α i β j γ k}
       → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
       → (n₁ n₂ p : Atom#) {diff : n₁ ≢ n₂}
       → ℂ α γ {i} {k} → ℂ β γ {j} {k} → ℂ (α ⊎ β) γ {suc (i ⊔ j)} {k}
|+ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ n₁ n₂ p {d} (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓W⇑-⊎ n₁ n₂ p {d} sα sβ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)
\end{code}
%</sum>

\begin{code}
infixr 9 _||_
infixl 8 _⟫_
\end{code}


%<*lemma-comb-seq>
\begin{code}
_comb⟫_ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
               → {c₁ : ℂ α β {i} {j}} {c₂ : ℂ β γ {j} {k}} → comb c₁ → comb c₂ → comb (c₁ ⟫ c₂)
_comb⟫_ {i = i} {j = j} {k = k} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} p₁ p₂ = _comb⟫'_ {i} {j} {k} {c₁'} {c₂'} p₁ p₂
\end{code}
%</lemma-comb-seq>

%<*lemma-comb-par>
\begin{code}
_comb|_ : ∀ {α i γ k β j δ l} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ ⦃ sδ : ⇓W⇑ δ {l} ⦄
               → {c₁ : ℂ α γ {i} {k}} {c₂ : ℂ β δ {j} {l}} → comb c₁ → comb c₂ → comb (c₁ || c₂)
_comb|_ {i = i} {k = k} {j = j} {l = l} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} p₁ p₂ = _comb|'_ {i} {k} {j} {l} {c₁'} {c₂'} p₁ p₂
\end{code}
%</lemma-comb-par>

%<*lemma-comb-sum>
\begin{code}
comb|+ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
         → {c₁ : ℂ α γ {i} {k}} {c₂ : ℂ β γ {j} {k}}
         → {n₁ n₂ p : Atom#} {diff : n₁ ≢ n₂} → comb c₁ → comb c₂ → comb (|+ n₁ n₂ p {diff} c₁ c₂)
comb|+ {i = i} {j = j} {k = k} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} p₁ p₂ = _comb|+'_ {i} {j} {k} {c₁'} {c₂'} p₁ p₂
\end{code}
%</lemma-comb-sum>
