module PiWare.Circuit (Atom : Set) where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)

open import PiWare.Synthesizable Atom
open import PiWare.Circuit.Core


-- "High-level" circuit datatype, packing the synthesis information
data ℂ (α β : Set) {#α #β : ℕ} : Set where
    Mkℂ : ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → Coreℂ Atom #α #β → ℂ α β {#α} {#β}


-- "Smart constructors"
_⟫_ : {α β γ : Set} {#α #β #γ : ℕ}
      ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
      → ℂ α β {#α} {#β} → ℂ β γ {#β} {#γ} → ℂ α γ {#α} {#γ}
_⟫_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ >> c₂)

_||_ : {i₁ o₁ i₂ o₂ : Set} {#i₁ #o₁ #i₂ #o₂ : ℕ}
       ⦃ si₁ : ⇓𝕎⇑ i₁ {#i₁} ⦄ ⦃ so₁ : ⇓𝕎⇑ o₁ {#o₁} ⦄ ⦃ si₂ : ⇓𝕎⇑ i₂ {#i₂} ⦄ ⦃ so₂ : ⇓𝕎⇑ o₂ {#o₂} ⦄
       → ℂ i₁ o₁ {#i₁} {#o₁} → ℂ i₂ o₂ {#i₂} {#o₂} →  ℂ (i₁ × i₂) (o₁ × o₂) {#i₁ + #i₂} {#o₁ + #o₂}
_||_ ⦃ si₁ ⦄ ⦃ so₁ ⦄ ⦃ si₂ ⦄ ⦃ so₂ ⦄ (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ  ⦃ ⇓𝕎⇑-× ⦃ si₁ ⦄ ⦃ si₂ ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ so₁ ⦄ ⦃ so₂ ⦄ ⦄  (c₁ >< c₂)

infixr 7 _||_
infixl 6 _⟫_
