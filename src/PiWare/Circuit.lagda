\begin{code}
open import PiWare.Atom

module PiWare.Circuit (At : Atomic) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Synthesizable At
open import PiWare.Circuit.Core

open Atomic At using (Atom#) 
\end{code}


-- "High-level" circuit types, packing the synthesizable instances
\begin{code}
data ℂ (α β : Set) {i j : ℕ} : Set where
    Mkℂ : ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ' At i j → ℂ α β {i} {j}
\end{code}

\begin{code}
comb : ∀ {α i β j} → ℂ α β {i} {j} → Set
comb (Mkℂ c') = comb' c'
\end{code}


-- "Smart constructors"
\begin{code}
delayℂ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
         → (c : ℂ (α × γ) (β × γ) {i + k} {j + k}) {p : comb c} → ℂ α β {i} {j}
delayℂ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c') {p} = Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c' {p})
\end{code}

\begin{code}
_⟫_ : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
      → ℂ α β {i} {j} → ℂ β γ {j} {k} → ℂ α γ {i} {k}
_⟫_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫' c₂)
\end{code}

\begin{code}
_||_ : ∀ {α i γ k β j δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
       → ℂ α γ {i} {k} → ℂ β δ {j} {l} →  ℂ (α × β) (γ × δ) {i + j} {k + l}
_||_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ ⇓𝕎⇑-× sγ sδ ⦄ (c₁ |' c₂)
\end{code}

\begin{code}
_|+_ : ∀ {α i β j γ k} → (n₁ n₂ p : Atom#) {diff : n₁ ≢ n₂}
       → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ α γ {i} {k} → ℂ β γ {j} {k} → ℂ (α ⊎ β) γ {suc (i ⊔ j)} {k}
_|+_ n₁ n₂ p ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ ⇓𝕎⇑-⊎ n₁ n₂ p sα sβ ⦄ ⦃ sγ ⦄ (c₁ |+' c₂)
\end{code}

\begin{code}
infixr 9 _||_
infixr 9 _|+_
infixl 8 _⟫_
\end{code}
