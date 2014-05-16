module PiWare.Circuit (Atom : Set) where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)

open import PiWare.Synthesizable Atom
open import PiWare.Circuit.Core


-- "High-level" circuit datatype, packing the synthesis information
data ℂ (α β : Set) {#α #β : ℕ} : Set where
    Mkℂ : ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → Combℂ Atom #α #β → ℂ α β {#α} {#β}

data ℂ* (α β : Set) {#α #β : ℕ} : Set where
    Mkℂ* : ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → Coreℂ Atom #α #β → ℂ* α β {#α} {#β}


-- "Smart constructors"
_⟫_ : {α β γ : Set} {#α #β #γ : ℕ}
      ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
      → ℂ α β {#α} {#β} → ℂ β γ {#β} {#γ} → ℂ α γ {#α} {#γ}
_⟫_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ >> c₂)

_||_ : {α γ β δ : Set} {#α #γ #β #δ : ℕ}
       ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
       → ℂ α γ {#α} {#γ} → ℂ β δ {#β} {#δ} →  ℂ (α × β) (γ × δ) {#α + #β} {#γ + #δ}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄  (c₁ >< c₂)

infixr 9 _||_
infixl 8 _⟫_


repeatC : {α β : Set} {#α #β : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄
          → ℂ α β {#α} {#β} → ℂ* α β {#α} {#β}
repeatC ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c) = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (Comb c)

delayLoopC : {α β γ : Set} {#α #β #γ : ℕ}
             ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
             → ℂ (α × γ) (β × γ) {#α + #γ} {#β + #γ} → ℂ* α β {#α} {#β}
delayLoopC ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c) = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (Delayed c)

_⟫*_ : {α β γ : Set} {#α #β #γ : ℕ}
       ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ* α β {#α} {#β} → ℂ* β γ {#β} {#γ} → ℂ* α γ {#α} {#γ}
_⟫*_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ >> c₂)

_||*_ : {α γ β δ : Set} {#α #γ #β #δ : ℕ}
        ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
        → ℂ* α γ {#α} {#γ} → ℂ* β δ {#β} {#δ} →  ℂ* (α × β) (γ × δ) {#α + #β} {#γ + #δ}
_||*_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) =
    Mkℂ*  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄  (c₁ >< c₂)

infixr 7 _||*_
infixl 6 _⟫*_
