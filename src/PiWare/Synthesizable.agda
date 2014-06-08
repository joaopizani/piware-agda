open import PiWare.Atom

module PiWare.Synthesizable (AI : AtomInfo) where

-- opening with the AtomInfo we just got, for convenience
open module AI' = AtomInfo AI

open import Function using (_$_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Bool using (if_then_else_) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _+_; _*_; _≟_; _≤?_; suc; _⊔_; decTotalOrder; s≤s; z≤n)
open import Data.Fin using (Fin; toℕ; #_)
open import Data.Vec using (Vec; _++_; splitAt; _>>=_; group; concat; map) renaming (_∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (refl; _≢_)
open import Relation.Nullary.Decidable using (True; fromWitness)
open import Relation.Nullary.Core using (yes; no)

open import PiWare.Padding


-- Words are sequences of "Atoms"
𝕎 : ℕ → Set
𝕎 = Vec Atom


-- Provides a mapping between "high-level" metalanguage types and words
record ⇓𝕎⇑ (α : Set) {i : ℕ} : Set where
    constructor ⇓𝕎⇑[_,_]
    field
        ⇓ : α → 𝕎 i
        ⇑ : 𝕎 i → α

open ⇓𝕎⇑ {{...}}


-- basic instances
⇓𝕎⇑-× : ∀ {α i β j} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α × β)
⇓𝕎⇑-× {α} {i} {β} {j} sα sβ = ⇓𝕎⇑[ down , up ]
    where down : (α × β) → 𝕎 (i + j)
          down (a , b) = (⇓ a) ++ (⇓ b)

          up : 𝕎 (i + j) → (α × β)
          up atoms with splitAt i atoms
          up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = (⇑ ⇓a) , (⇑ ⇓b)

⇓𝕎⇑-Vec : ∀ {α i n} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (Vec α n)
⇓𝕎⇑-Vec {α} {i} {n} sα = ⇓𝕎⇑[ down , up ]
    where down : Vec α n → 𝕎 (n * i)
          down v = v >>= ⇓

          up : 𝕎 (n * i) → Vec α n
          up atoms with group n i atoms
          up .(concat grps) | grps , refl = map ⇑ grps

-- TODO: guarantee that n₁ and n₂ are different?
⇓𝕎⇑-⊎' : ∀ {α i β j} → (n₁ n₂ p : Atom#) → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α ⊎ β) {suc (i ⊔ j)}
⇓𝕎⇑-⊎' {α} {i} {β} {j} n₁ n₂ p sα sβ = ⇓𝕎⇑[ down , up ]
    where down : α ⊎ β → 𝕎 (suc (i ⊔ j))
          down = [ (λ a → (n→atom n₁) ◁ padFst i j (n→atom p) (⇓ a))
                 , (λ b → (n→atom n₂) ◁ padSnd i j (n→atom p) (⇓ b)) ]
          
          up : 𝕎 (suc (i ⊔ j)) → α ⊎ β
          up (t ◁ ab) with toℕ (atom→n t) ≟ toℕ n₂
          up (t ◁ ab) | yes p = inj₂ $ ⇑ (unpadSnd i j ab)
          up (t ◁ ab) | no ¬p = inj₁ $ ⇑ (unpadFst i j ab)

import Relation.Binary as RB
open module NatDTO = RB.DecTotalOrder decTotalOrder using (trans)

⇓𝕎⇑-⊎ : ∀ {α i β j} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α ⊎ β) {suc (i ⊔ j)}
⇓𝕎⇑-⊎ {α} {i} {β} {j} sα sβ = ⇓𝕎⇑-⊎' {α} {i} {β} {j} (# 0) (# 1) (# 0) sα sβ
    where
        fin0≤?card : True (suc 0 ≤? card)
        fin0≤?card = fromWitness (trans (s≤s z≤n) card≥2)

        fin1≤?card : True (suc 1 ≤? card)
        fin1≤?card = fromWitness (trans (s≤s (s≤s z≤n)) card≥2)


-- derivable instances (can be resolved recursively from the basic)
⇓𝕎⇑-[a×b]×c : ∀ {α i β j γ k} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ ((α × β) × γ)
⇓𝕎⇑-a×[b×c] : ∀ {α i β j γ k} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ (α × (β × γ))

⇓𝕎⇑-a×[b×c] sα sβ sγ = ⇓𝕎⇑-× sα            (⇓𝕎⇑-× sβ sγ)
⇓𝕎⇑-[a×b]×c sα sβ sγ = ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ


⇓𝕎⇑-a×[b×[c×d]] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (α × (β × (γ × δ)))
⇓𝕎⇑-a×[[b×c]×d] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (α × ((β × γ) × δ))
⇓𝕎⇑-[a×b]×[c×d] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ ((α × β) × (γ × δ))
⇓𝕎⇑-[a×[b×c]]×d : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ ((α × (β × γ)) × δ)
⇓𝕎⇑-[[a×b]×c]×d : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (((α × β) × γ) × δ)

⇓𝕎⇑-a×[b×[c×d]] sα sβ sγ sδ = ⇓𝕎⇑-× sα                     (⇓𝕎⇑-a×[b×c] sβ sγ sδ)
⇓𝕎⇑-a×[[b×c]×d] sα sβ sγ sδ = ⇓𝕎⇑-× sα                     (⇓𝕎⇑-[a×b]×c sβ sγ sδ)
⇓𝕎⇑-[a×[b×c]]×d sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-a×[b×c] sα sβ sγ) sδ
⇓𝕎⇑-[[a×b]×c]×d sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-[a×b]×c sα sβ sγ) sδ
⇓𝕎⇑-[a×b]×[c×d] sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) (⇓𝕎⇑-× sγ sδ)


⇓𝕎⇑-a×[Vec[b]] : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α × Vec β n)
⇓𝕎⇑-Vec[a]×b   : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (Vec α n × β)
⇓𝕎⇑-Vec[a×b]   : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (Vec (α × β) n)

⇓𝕎⇑-a×[Vec[b]] {n = m} sα sβ = ⇓𝕎⇑-× sα           (⇓𝕎⇑-Vec sβ)
⇓𝕎⇑-Vec[a]×b   {n = m} sα sβ = ⇓𝕎⇑-× (⇓𝕎⇑-Vec sα) sβ
⇓𝕎⇑-Vec[a×b]   {n = m} sα sβ = ⇓𝕎⇑-Vec {n = m} (⇓𝕎⇑-× sα sβ)
