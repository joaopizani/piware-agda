module PiWare.Synthesizable (Atom : Set) where

open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Vec using (Vec; _++_; splitAt; _>>=_; group; concat; map)

open import Relation.Binary.PropositionalEquality using (refl)


-- Words are sequences of "Atoms"
𝕎 : ℕ → Set
𝕎 = Vec Atom


-- Provides a mapping between "high-level" metalanguage types and words
record ⇓𝕎⇑ (α : Set) {#α : ℕ} : Set where
    constructor ⇓𝕎⇑[_,_]
    field
        ⇓ : α → 𝕎 #α
        ⇑ : 𝕎 #α → α

open ⇓𝕎⇑ {{...}}

-- basic instances
⇓𝕎⇑-× : {α β : Set} {#α #β : ℕ} ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → ⇓𝕎⇑ (α × β)
⇓𝕎⇑-× {α} {β} {#α} {#β} = ⇓𝕎⇑[ down , up ]
    where down : (α × β) → 𝕎 (#α + #β)
          down (a , b) = (⇓ a) ++ (⇓ b)

          up : 𝕎 (#α + #β) → (α × β)
          up atoms with splitAt #α atoms
          up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = (⇑ ⇓a) , (⇑ ⇓b)

⇓𝕎⇑-Vec : {α : Set} {#α n : ℕ} ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (Vec α n)
⇓𝕎⇑-Vec {α} {#α} {n} = ⇓𝕎⇑[ down , up ]
    where down : Vec α n → 𝕎 (n * #α)
          down v = v >>= ⇓

          up : 𝕎 (n * #α) → Vec α n
          up atoms with group n #α atoms
          up .(concat grps) | grps , refl = map ⇑ grps



-- derivable instances (can be resolved recursively from the basic)
⇓𝕎⇑-a×[b×c] : {α β γ : Set} {#α #β #γ : ℕ}
               → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
               → ⇓𝕎⇑ (α × (β × γ))
⇓𝕎⇑-a×[b×c] ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦄

⇓𝕎⇑-[a×b]×c : {α β γ : Set} {#α #β #γ : ℕ}
               → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
               → ⇓𝕎⇑ ((α × β) × γ)
⇓𝕎⇑-[a×b]×c ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ sγ ⦄


⇓𝕎⇑-a×[b×[c×d]] : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
                 → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
                 → ⇓𝕎⇑ (α × (β × (γ × δ)))
⇓𝕎⇑-a×[b×[c×d]] ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-a×[b×c] ⦄

⇓𝕎⇑-a×[[b×c]×d] : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
                 → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
                 → ⇓𝕎⇑ (α × ((β × γ) × δ))
⇓𝕎⇑-a×[[b×c]×d] ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-[a×b]×c ⦄

⇓𝕎⇑-[a×b]×[c×d] : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
                 → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
                 → ⇓𝕎⇑ ((α × β) × (γ × δ))
⇓𝕎⇑-[a×b]×[c×d] ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄

⇓𝕎⇑-[a×[b×c]]×d : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
                 → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
                 → ⇓𝕎⇑ ((α × (β × γ)) × δ)
⇓𝕎⇑-[a×[b×c]]×d ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-a×[b×c] ⦄ ⦃ sδ ⦄

⇓𝕎⇑-[[a×b]×c]×d : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
                 → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
                 → ⇓𝕎⇑ (((α × β) × γ) × δ)
⇓𝕎⇑-[[a×b]×c]×d ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-[a×b]×c ⦄ ⦃ sδ ⦄


⇓𝕎⇑-a×[Vec[b]] : {α β : Set} {#α #β : ℕ} {n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄
                  → ⇓𝕎⇑ (α × Vec β n)
⇓𝕎⇑-a×[Vec[b]] {n = k} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec ⦄

⇓𝕎⇑-Vec[a]×b : {α β : Set} {#α #β : ℕ} {n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄
                → ⇓𝕎⇑ (Vec α n × β)
⇓𝕎⇑-Vec[a]×b {n = k} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-Vec ⦄ ⦃ sβ ⦄

⇓𝕎⇑-Vec[a×b] : {α β : Set} {#α #β : ℕ} {n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄
                → ⇓𝕎⇑ (Vec (α × β) n)
⇓𝕎⇑-Vec[a×b] {n = k} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓𝕎⇑-Vec {n = k} ⦃ ⇓𝕎⇑-× ⦄ 
