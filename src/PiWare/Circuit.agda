module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; [_]; _++_)


-- Core Circuit type
data ℂ (α : Set) : ℕ → ℕ → Set where
    -- Fundamental building blocks
    Not : ℂ α 1 1
    And : ℂ α 2 1
    Or  : ℂ α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → ℂ α i o
    _⟫_  : {i m o : ℕ} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : {i₁ o₁ i₂ o₂ : ℕ} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ + i₂) (o₁ + o₂)

infixl 5 _||_
infixl 4 _⟫_

-- "Algebra" for evaluating a circuit, closely related to the ℂ type itself.
-- Each field of the algebra corresponds to a "fundamental" constructor of ℂ
record Algℂ (α : Set) : Set where
   constructor algℂ[_,_,_]
   field
       ¬ : α → α
       ∧ : α → α → α
       ∨ : α → α → α


-- Provides a mapping between "high-level" metalanguage types and vectors of bits
record Synthesizable (α : Set) : Set where
    constructor Synth[_,_]
    field
        # : ℕ  -- size
        ⇓ : α → Vec Bool #  -- mapping to bit vectors

open Synthesizable {{...}}

Circuit : (i o : Set) ⦃ _ : Synthesizable i ⦄ ⦃ _ : Synthesizable o ⦄ → Set
Circuit i o ⦃ si ⦄ ⦃ so ⦄ = ℂ Bool (# {i} ⦃ si ⦄) (# {o} ⦃ so ⦄)

synthBool : Synthesizable Bool
synthBool = Synth[ 1 , toVec ]
    where toVec : Bool → Vec Bool 1
          toVec b = [ b ]

synthPair : {α β : Set} ⦃ _ : Synthesizable α ⦄ ⦃ _ : Synthesizable β ⦄ → Synthesizable (α × β)
synthPair {α} {β} ⦃ sα ⦄ ⦃ sβ ⦄ = Synth[ pairSize , toVec ]
    where pairSize : ℕ
          pairSize = (# {α} ⦃ sα ⦄) + (# {β} ⦃ sβ ⦄)

          toVec : (α × β) → Vec Bool pairSize
          toVec (a , b) = (⇓ a) ++ (⇓ b)

synthBoolPair : Synthesizable (Bool × Bool)
synthBoolPair = synthPair {Bool} {Bool}



-- "Smart constructors"

¬ : Circuit Bool Bool
¬ = Not

∧ : Circuit (Bool × Bool) Bool
∧ = And

∨ : Circuit (Bool × Bool) Bool
∨ = Or

_>>_ : {α β γ : Set} ⦃ sα : Synthesizable α ⦄ ⦃ sβ : Synthesizable β ⦄ ⦃ sγ : Synthesizable γ ⦄
       → Circuit α β → Circuit β γ → Circuit α γ
_>>_ c₁ c₂ = c₁ ⟫ c₂

_><_ : {i₁ o₁ i₂ o₂ : Set}
       ⦃ si₁ : Synthesizable i₁ ⦄ ⦃ so₁ : Synthesizable o₁ ⦄ ⦃ si₂ : Synthesizable i₂ ⦄ ⦃ so₂ : Synthesizable o₂ ⦄
       → Circuit i₁ o₁ → Circuit i₂ o₂
       → Circuit (i₁ × i₂) (o₁ × o₂) ⦃ synthPair ⦃ si₁ ⦄ ⦃ si₂ ⦄ ⦄  ⦃ synthPair ⦃ so₁ ⦄ ⦃ so₂ ⦄ ⦄
_><_ c₁ c₂ = c₁ || c₂

⑂ : {α : Set} ⦃ sα : Synthesizable α ⦄  →  Circuit α (α × α) ⦃ sα ⦄ ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄
⑂ {α} ⦃ sα ⦄ = Plug {Bool} {# ⦃ sα ⦄} {# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄} ⑂'
    where ⑂' : Fin (# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄) → Fin (# ⦃ sα ⦄)
          ⑂' x = {!!}
