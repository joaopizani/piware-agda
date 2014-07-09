\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Correctness {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (_++_; splitAt)
open import Data.Product using (_,_) renaming (map to mapₚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import PiWare.Synthesizable At
open ⇓𝕎⇑ ⦃ ... ⦄

open import PiWare.Circuit.Core Gt using (ℂ'; _⟫'_; _|'_; comb'; _comb⟫'_; _comb|'_)
open import PiWare.Circuit Gt using (ℂ; Mkℂ; comb; _⟫_; _||_; _comb⟫_; _comb|_; comb|+)
open import PiWare.Simulation.Core Gt using (⟦_⟧')
open import PiWare.Simulation Gt using (⟦_⟧)
\end{code}


%<*seqproof'>
\begin{code}
_⟫≡'_ : {i m o : ℕ} {f₁ : 𝕎 i → 𝕎 m} {f₂ : 𝕎 m → 𝕎 o}
        {c₁ : ℂ' i m} {c₂ : ℂ' m o} {p₁ : comb' c₁} {p₂ : comb' c₂}
        → ((v₁ : 𝕎 i) → ⟦_⟧' {i} {m} c₁ {p₁} v₁ ≡ f₁ v₁) → ((v₂ : 𝕎 m) → ⟦_⟧' {m} {o} c₂ {p₂} v₂ ≡ f₂ v₂)
        → ((v : 𝕎 i) → ⟦_⟧' {i} {o} (c₁ ⟫' c₂) {p₁ comb⟫' p₂} v ≡ (f₂ ∘ f₁) v)
_⟫≡'_ {f₁ = f₁} pc₁ pc₂ v rewrite sym (pc₂ (f₁ v)) | sym (pc₁ v) = refl
\end{code}
%</seqproof'>

%<*parproof'>
\begin{code}
_|≡'_ : {i₁ o₁ i₂ o₂ : ℕ} {f₁ : 𝕎 i₁ → 𝕎 o₁} {f₂ : 𝕎 i₂ → 𝕎 o₂}
        {c₁ : ℂ' i₁ o₁} {c₂ : ℂ' i₂ o₂} {p₁ : comb' c₁} {p₂ : comb' c₂}
        → ((v₁ : 𝕎 i₁) → ⟦_⟧' {i₁} {o₁} c₁ {p₁} v₁ ≡ f₁ v₁) → ((v₂ : 𝕎 i₂) → ⟦_⟧' {i₂} {o₂} c₂ {p₂} v₂ ≡ f₂ v₂)
        → ((v₁ : 𝕎 i₁) (v₂ : 𝕎 i₂) → ⟦_⟧' {i₁ + i₂} {o₁ + o₂} (c₁ |' c₂) {p₁ comb|' p₂} (v₁ ++ v₂) ≡ f₁ v₁ ++ f₂ v₂)
_|≡'_ {i₁ = i₁} {f₁ = f₁} pc₁ pc₂ v₁ v₂ with splitAt i₁ (v₁ ++ v₂)
_|≡'_ {i₁ = i₁} {f₁ = f₁} pc₁ pc₂ v₁ v₂ | w₁ , w₂ , r = {!!}
\end{code}
%</parproof'>



%<*spec-down>
\begin{code}
spec⇓ : ∀ {α i β j} → {c' : ℂ' i j} {f : 𝕎 i → 𝕎 j} {p : comb' c'} ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄
        → ((x : α) → ⟦_⟧ {α} {i} {β} {j} (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') {p} x ≡ ⇑ ⦃ sβ ⦄ (f (⇓ ⦃ sα ⦄ x)) )
        → ((v : 𝕎 i) → ⟦_⟧' {i} {j} c' {p} v ≡ f v)
spec⇓ ⦃ sα = sα ⦄ p⇑ v = {!!}
\end{code}
%</spec-down>


%<*seqproof>
\begin{code}
_⟫≡_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → {f₁ : α → β} {f₂ : β → γ} {c₁ : ℂ α β {i} {j}} {c₂ : ℂ β γ {j} {k}} {p₁ : comb c₁} {p₂ : comb c₂}
       → ((x₁ : α) → ⟦_⟧ {α} {i} {β} {j} c₁ {p₁} x₁ ≡ f₁ x₁)
       → ((x₂ : β) → ⟦_⟧ {β} {j} {γ} {k} c₂ {p₂} x₂ ≡ f₂ x₂)
       → ((x : α)  → ⟦_⟧ {α} {i} {γ} {k} (c₁ ⟫ c₂) {p₁ comb⟫ p₂} x ≡ (f₂ ∘ f₁) x)
_⟫≡_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ {f₁ = f₁} {f₂ = f₂} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} pc₁ pc₂ x = {!!}
\end{code}
%</seqproof>


%<*parproof>
\begin{code}
_|≡_ : ∀ {α i β j γ k δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → {f₁ : α → γ} {c₁ : ℂ α γ {i} {k}} {f₂ : β → δ} {c₂ : ℂ β δ {j} {l}}
       → {p₁ : comb c₁} {p₂ : comb c₂} {x₁ : α} {x₂ : β}
       → ⟦_⟧ {i = i} {j = k} c₁ {p₁} x₁ ≡ f₁ x₁  →  ⟦_⟧ {i = j} {j = l} c₂ {p₂} x₂ ≡ f₂ x₂
       → ⟦_⟧ {i = i + j} {j = k + l} (c₁ || c₂) {p₁ comb| p₂} (x₁ , x₂) ≡ mapₚ f₁ f₂ (x₁ , x₂)
pc₁ |≡ pc₂ = {!!}
\end{code}
%</parproof>
