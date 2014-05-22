open import PiWare.Atom

module PiWare.Circuit (AI : AtomInfo) where

open module AI' = AtomInfo AI

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

open import PiWare.Synthesizable AI
open import PiWare.Circuit.Core


-- "High-level" circuit types, packing the synthesis information
data ℂ (α β : Set) {#α #β : ℕ} : Set where
    Mkℂ : ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → ℂ' Atom #α #β → ℂ α β {#α} {#β}

data ℂ* (α β : Set) {#α #β : ℕ} : Set where
    Mkℂ* : ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → ℂ'* Atom #α #β → ℂ* α β {#α} {#β}


-- "Smart constructors"
_⟫_ : {α β γ : Set} {#α #β #γ : ℕ}
      ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
      → ℂ α β {#α} {#β} → ℂ β γ {#β} {#γ} → ℂ α γ {#α} {#γ}
_⟫_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)

_||_ : {α γ β δ : Set} {#α #γ #β #δ : ℕ}
       ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
       → ℂ α γ {#α} {#γ} → ℂ β δ {#β} {#δ} →  ℂ (α × β) (γ × δ) {#α + #β} {#γ + #δ}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄  (c₁ |' c₂)

_|+_ : {α β γ : Set} {#α #β #γ : ℕ}
       ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ α γ {#α} {#γ} → ℂ β γ {#β} {#γ} → ℂ (α ⊎ β) γ {suc (#α ⊔ #β)} {#γ}
_|+_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓𝕎⇑-⊎ ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)

infixr 9 _||_
infixr 9 _|+_
infixl 8 _⟫_


repeatℂ : {α β : Set} {#α #β : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄
          → ℂ α β {#α} {#β} → ℂ* α β {#α} {#β}
repeatℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c) = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (Comb c)

delayℂ : {α β γ : Set} {#α #β #γ : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
         → ℂ (α × γ) (β × γ) {#α + #γ} {#β + #γ} → ℂ* α β {#α} {#β}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c) = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c)

_⟫*_ : {α β γ : Set} {#α #β #γ : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ* α β {#α} {#β} → ℂ* β γ {#β} {#γ} → ℂ* α γ {#α} {#γ}
_⟫*_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫'* c₂)

_|*_ : {α γ β δ : Set} {#α #γ #β #δ : ℕ}
       ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
       → ℂ* α γ {#α} {#γ} → ℂ* β δ {#β} {#δ} →  ℂ* (α × β) (γ × δ) {#α + #β} {#γ + #δ}
_|*_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) =
    Mkℂ*  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄  (c₁ |'* c₂)

_|+*_ : {α β γ : Set} {#α #β #γ : ℕ}
        ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
        → ℂ* α γ {#α} {#γ} → ℂ* β γ {#β} {#γ} → ℂ* (α ⊎ β) γ {suc (#α ⊔ #β)} {#γ}
_|+*_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ ⇓𝕎⇑-⊎ ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ (c₁ |+'* c₂)

infixr 7 _|*_
infixr 7 _|+*_
infixl 6 _⟫*_
