module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)

open import PiWare.Synthesizable.Bool
open import PiWare.Circuit.Core


-- "High-level" circuit datatype, packing the synthesis information
data ℂ (i o : Set) {#i #o : ℕ} : Set where
    Mkℂ : ⦃ _ : ⇓𝕎⇑ i {#i} ⦄ ⦃ _ : ⇓𝕎⇑ o {#o} ⦄ → Coreℂ 𝔹 #i #o → ℂ i o {#i} {#o}

-- "Smart constructors"
¬ : ℂ 𝔹 𝔹
¬ = Mkℂ Not

∧ : ℂ (𝔹 × 𝔹) 𝔹
∧ = Mkℂ And

∨ : ℂ (𝔹 × 𝔹) 𝔹
∨ = Mkℂ Or

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
