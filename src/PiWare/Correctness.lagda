\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Correctness {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_) renaming (map to mapₚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import PiWare.Synthesizable At using (⇓𝕎⇑)
open import PiWare.Circuit Gt using (ℂ; comb; _⟫_; _||_)
open import PiWare.Simulation Gt using (⟦_⟧)
\end{code}


proof "combinators"
%<*proofComb-seq>
\begin{code}
_⟫≡_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → {f₁ : α → β} {c₁ : ℂ α β {i} {j}} {f₂ : β → γ} {c₂ : ℂ β γ {j} {k}}
       → {p₁ : comb c₁} {p₂ : comb c₂} {x : α}
       → ⟦_⟧ {i = i} {j = j} c₁ {p₁} x ≡ f₁ x  →  ⟦_⟧ {i = j} {j = k} c₂ {p₂} (f₁ x) ≡ f₂ (f₁ x)
       → ⟦_⟧ {i = i} {j = k} (c₁ ⟫ c₂) {{!p₁ , p₂!}} x ≡ f₂ (f₁ x)
pc₁ ⟫≡ pc₂ rewrite sym pc₁ | sym pc₂ = {!refl!}
\end{code}
%</proofComb-seq>


%<*proofComb-par>
\begin{code}
_|≡_ : ∀ {α i β j γ k δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → {f₁ : α → γ} {c₁ : ℂ α γ {i} {k}} {f₂ : β → δ} {c₂ : ℂ β δ {j} {l}}
       → {p₁ : comb c₁} {p₂ : comb c₂} {x₁ : α} {x₂ : β}
       → ⟦_⟧ {i = i} {j = k} c₁ {p₁} x₁ ≡ f₁ x₁  →  ⟦_⟧ {i = j} {j = l} c₂ {p₂} x₂ ≡ f₂ x₂
       → ⟦_⟧ {i = i + j} {j = k + l} (c₁ || c₂) {{!p₁ , p₂!}} (x₁ , x₂) ≡ mapₚ f₁ f₂ (x₁ , x₂)
pc₁ |≡ pc₂ rewrite sym pc₁ | sym pc₂ = {!refl!}
\end{code}
%</proofComb-par>
