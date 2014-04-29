module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; [_]; _++_; _>>=_)


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
record Synth (α : Set) {#α : ℕ} : Set where
    constructor Synth[_]
    field ⇓ : α → Vec Bool #α  -- mapping to bit vectors

open Synth {{...}}


data Circ (i o : Set) {#i #o : ℕ} : Set where
  MkCirc : ⦃ si : Synth i {#i} ⦄ ⦃ so : Synth o {#o} ⦄ → ℂ Bool #i #o → Circ i o {#i} {#o}

synthBool : Synth Bool
synthBool = Synth[ toVec ]
    where toVec : Bool → Vec Bool _
          toVec b = [ b ]

synthPair : {α β : Set} {#α #β : ℕ} ⦃ _ : Synth α {#α} ⦄ ⦃ _ : Synth β {#β} ⦄
            → Synth (α × β) {#α + #β}
synthPair {α} {β} = Synth[ toVec ]
    where toVec : (α × β) → Vec Bool _
          toVec (a , b) = (⇓ a) ++ (⇓ b)

synthVec : {α : Set} {#α n : ℕ} ⦃ _ : Synth α {#α} ⦄
           → Synth (Vec α n) {n * #α}
synthVec {α} {_} {n} = Synth[ toVec ]
    where toVec : Vec α n → Vec Bool _
          toVec v = v >>= ⇓

-- TODO: why doesn't this work in a where binding (or let)?
synthBoolPair : Synth (Bool × Bool)
synthBoolPair = synthPair

synthBoolVec : ∀ {n} → Synth (Vec Bool n)
synthBoolVec = synthVec

synthBoolVec2 : Synth (Vec Bool 2)
synthBoolVec2 = synthBoolVec



-- "Smart constructors"
¬ : Circ Bool Bool
¬ = MkCirc Not

∧ : Circ (Bool × Bool) Bool
∧ = MkCirc And

∨ : Circ (Bool × Bool) Bool
∨ = MkCirc Or

_>>_ : {α β γ : Set} {#α #β #γ : ℕ} ⦃ sα : Synth α {#α} ⦄ ⦃ sβ : Synth β {#β} ⦄ ⦃ sγ : Synth γ {#γ} ⦄
       → Circ α β {#α} {#β} → Circ β γ {#β} {#γ} → Circ α γ {#α} {#γ}
_>>_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (MkCirc c₁) (MkCirc c₂) = MkCirc ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫ c₂)

testNotNot : Circ Bool Bool
testNotNot = ¬ >> ¬

_><_ : {i₁ o₁ i₂ o₂ : Set} {#i₁ #o₁ #i₂ #o₂ : ℕ}
       ⦃ si₁ : Synth i₁ {#i₁} ⦄ ⦃ so₁ : Synth o₁ {#o₁} ⦄ ⦃ si₂ : Synth i₂ {#i₂} ⦄ ⦃ so₂ : Synth o₂ {#o₂} ⦄
       → Circ i₁ o₁ {#i₁} {#o₁}
       → Circ i₂ o₂ {#i₂} {#o₂}
       → Circ (i₁ × i₂) (o₁ × o₂) {#i₁ + #i₂} {#o₁ + #o₂}
_><_ ⦃ si₁ ⦄ ⦃ so₁ ⦄ ⦃ si₂ ⦄ ⦃ so₂ ⦄ (MkCirc c₁) (MkCirc c₂) =
    MkCirc  ⦃ synthPair ⦃ si₁ ⦄ ⦃ si₂ ⦄ ⦄  ⦃ synthPair ⦃ so₁ ⦄ ⦃ so₂ ⦄ ⦄  (c₁ || c₂)


testAndTree : Circ ((Bool × Bool) × (Bool × Bool)) Bool
testAndTree =
    let
        synthBoolPairPair : Synth ((Bool × Bool) × (Bool × Bool))
        synthBoolPairPair = synthPair
    in (∧ >< ∧) >> ∧

-- ⑂ : {α : Set} ⦃ sα : Synthesizable α ⦄  →  Circuit α (α × α) ⦃ sα ⦄ ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄
-- ⑂ {α} ⦃ sα ⦄ = Plug {Bool} {# ⦃ sα ⦄} {# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄} ⑂'
--     where ⑂' : Fin (# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄) → Fin (# ⦃ sα ⦄)
--           ⑂' x = {!!}



-- eval : {α β : Set} {n m : ℕ} → (s : Signal α β {n} {m}) → Vec Bool n → Vec Bool m
-- eval (MkSig {{sα}} {{sβ}} Not) i = {!!}
-- eval (MkSig {{sα}} {{sβ}} And) i = {!!}
-- eval (MkSig {{sα}} {{sβ}} Or) i = {!!}
-- eval (MkSig {{sα}} {{sβ}} (Plug f)) i₁ = {!!}
-- eval (MkSig {{sα}} {{sβ}} (x ⟫ x₁)) i₁ = {!!}
-- eval (MkSig {{sα}} {{sβ}} (x || x₁)) i = {!!}
