\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Correctness {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_) renaming (map to mapₚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import PiWare.Synthesizable At
open ⇓𝕎⇑ ⦃ ... ⦄

open import PiWare.Circuit.Core Gt using (ℂ'; _⟫'_; comb')
open import PiWare.Circuit Gt
open import PiWare.Simulation.Core Gt using (⟦_⟧')
open import PiWare.Simulation Gt using (⟦_⟧)
\end{code}


TODO: have the hypotheses working forall x
TODO: write high level in terms of low level
%<*seqproof>
\begin{code}
_⟫≡'_ : {i j k : ℕ} {f₁ : 𝕎 i → 𝕎 j} {f₂ : 𝕎 j → 𝕎 k}
        {c₁ : ℂ' i j} {c₂ : ℂ' j k} {p₁ : comb' c₁} {p₂ : comb' c₂}
        → (∀ x₁ → ⟦_⟧' {i} {j} c₁ {p₁} x₁ ≡ f₁ x₁) → (∀ x₂ → ⟦_⟧' {j} {k} c₂ {p₂} x₂ ≡ f₂ x₂)
        → (∀ x → ⟦_⟧' {i} {k} (c₁ ⟫' c₂) {p₁ , p₂} x ≡ (f₂ ∘ f₁) x)
_⟫≡'_ {f₁ = f₁} pc₁ pc₂ x rewrite pc₁ x | pc₂ (f₁ x) = refl


lemmaCombSeq : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
               → {c₁ : ℂ α β {i} {j}} {c₂ : ℂ β γ {j} {k}} → comb c₁ → comb c₂ → comb (c₁ ⟫ c₂)
lemmaCombSeq {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} p₁ p₂ = p₁ , p₂

spec⇓ : ∀ {α i β j} → {c' : ℂ' i j} {f : 𝕎 i → 𝕎 j} {p : comb' c'} ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄
        → ((x : α) → ⟦_⟧ {α} {i} {β} {j} (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') {p} x ≡ ⇑ ⦃ sβ ⦄ (f (⇓ ⦃ sα ⦄ x)) )
        → ((v : 𝕎 i) → ⟦_⟧' {i} {j} c' {p} v ≡ f v)
spec⇓ ⦃ sα = sα ⦄ p⇑ v = {!!}

_⟫≡_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → {f₁ : α → β} {f₂ : β → γ} {c₁ : ℂ α β {i} {j}} {c₂ : ℂ β γ {j} {k}} {p₁ : comb c₁} {p₂ : comb c₂}
       → ((x₁ : α) → ⟦_⟧ {α} {i} {β} {j} c₁ {p₁} x₁ ≡ f₁ x₁)
       → ((x₂ : β) → ⟦_⟧ {β} {j} {γ} {k} c₂ {p₂} x₂ ≡ f₂ x₂)
       → ((x : α)  → ⟦_⟧ {α} {i} {γ} {k} (c₁ ⟫ c₂) {lemmaCombSeq p₁ p₂} x ≡ (f₂ ∘ f₁) x)
_⟫≡_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ {f₁ = f₁} {f₂ = f₂} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} pc₁ pc₂ x = {!!}
\end{code}
%</seqproof>


%<*parproof>
\begin{code}
_|≡_ : ∀ {α i β j γ k δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → {f₁ : α → γ} {c₁ : ℂ α γ {i} {k}} {f₂ : β → δ} {c₂ : ℂ β δ {j} {l}}
       → {p₁ : comb c₁} {p₂ : comb c₂} {x₁ : α} {x₂ : β}
       → ⟦_⟧ {i = i} {j = k} c₁ {p₁} x₁ ≡ f₁ x₁  →  ⟦_⟧ {i = j} {j = l} c₂ {p₂} x₂ ≡ f₂ x₂
       → ⟦_⟧ {i = i + j} {j = k + l} (c₁ || c₂) {{!p₁ , p₂!}} (x₁ , x₂) ≡ mapₚ f₁ f₂ (x₁ , x₂)
pc₁ |≡ pc₂ = {!!}
\end{code}
%</parproof>
