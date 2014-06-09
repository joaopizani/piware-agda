open import PiWare.Atom

module PiWare.Circuit (AI : AtomInfo) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

open import PiWare.Synthesizable AI
open import PiWare.Circuit.Core


-- "High-level" circuit types, packing the synthesis information
data ℂ (α β : Set) {i j : ℕ} : Set where
    Mkℂ : ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ' AI i j → ℂ α β {i} {j}

data ℂ* (α β : Set) {i j : ℕ} : Set where
    Mkℂ* : ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ'* AI i j → ℂ* α β {i} {j}


-- "Smart constructors"

-- Combinational
_⟫_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
      → ℂ α β {i} {j} → ℂ β γ {j} {k} → ℂ α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)

_||_ : ∀ {α i γ k β j δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → ℂ α γ {i} {k} → ℂ β δ {j} {l} →  ℂ (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ ⇓𝕎⇑-× sγ sδ ⦄ (c₁ |' c₂)

_|+_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ α γ {i} {k} → ℂ β γ {j} {k} → ℂ (α ⊎ β) γ {suc (i ⊔ j)} {k}
_|+_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓𝕎⇑-⊎ sα sβ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)

infixr 9 _||_
infixr 9 _|+_
infixl 8 _⟫_


-- Sequential
repeatℂ : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ α β {i} {j} → ℂ* α β {i} {j}
repeatℂ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (Comb c')

delayℂ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ → ℂ (α × γ) (β × γ) {i + k} {j + k} → ℂ* α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c') = Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c')

_⟫*_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ → ℂ* α β {i} {j} → ℂ* β γ {j} {k} → ℂ* α γ {i} {k}
_⟫*_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫'* c₂)

_|*_ : ∀ {α i γ k β j δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → ℂ* α γ {i} {k} → ℂ* β δ {j} {l} →  ℂ* (α × β) (γ × δ) {i + j} {k + l}
_|*_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ ⇓𝕎⇑-× sγ sδ ⦄ (c₁ |'* c₂)

_|+*_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
        → ℂ* α γ {i} {k} → ℂ* β γ {j} {k} → ℂ* (α ⊎ β) γ {suc (i ⊔ j)} {k}
_|+*_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ* c₁) (Mkℂ* c₂) = Mkℂ* ⦃ ⇓𝕎⇑-⊎ sα sβ ⦄ ⦃ sγ ⦄ (c₁ |+'* c₂)

infixr 7 _|*_
infixr 7 _|+*_
infixl 6 _⟫*_
