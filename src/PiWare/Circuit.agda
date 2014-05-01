module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_; _*_; zero; suc)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (not; true; false) renaming (Bool to 𝔹; _∧_ to _and_; _∨_ to _or_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; [_]; _++_; _>>=_; splitAt; group; concat; map; lookup)
                     renaming (_∷_ to _◁_; [] to ε)
open import Relation.Binary.PropositionalEquality using (refl)


-- Core Circuit type
data Coreℂ (α : Set) : ℕ → ℕ → Set where
    -- Fundamental building blocks
    Not : Coreℂ α 1 1
    And : Coreℂ α 2 1
    Or  : Coreℂ α 2 1
    -- Structure-related
    Plug : {i o : ℕ} → (f : Fin o → Fin i) → Coreℂ α i o
    _>>_ : {i m o : ℕ} → Coreℂ α i m → Coreℂ α m o → Coreℂ α i o
    _><_ : {i₁ o₁ i₂ o₂ : ℕ} → Coreℂ α i₁ o₁ → Coreℂ α i₂ o₂ → Coreℂ α (i₁ + i₂) (o₁ + o₂)

infixl 5 _><_
infixl 4 _>>_

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
    constructor Synth[_,_]
    field
        ⇓ : α → Vec 𝔹 #α  -- to bit vectors
        ⇑ : Vec 𝔹 #α → α  -- from bit vectors

open Synth {{...}}


data ℂ (i o : Set) {#i #o : ℕ} : Set where
  Mkℂ : ⦃ si : Synth i {#i} ⦄ ⦃ so : Synth o {#o} ⦄ → Coreℂ 𝔹 #i #o → ℂ i o {#i} {#o}

synth𝔹 : Synth 𝔹
synth𝔹 = Synth[ toVec , fromVec ]
    where toVec : 𝔹 → Vec 𝔹 _
          toVec b = [ b ]
          
          fromVec : Vec 𝔹 _ → 𝔹
          fromVec (bit ◁ ε) = bit

synthPair : {α β : Set} {#α #β : ℕ} ⦃ _ : Synth α {#α} ⦄ ⦃ _ : Synth β {#β} ⦄
            → Synth (α × β) {#α + #β}
synthPair {α} {β} {#α} = Synth[ toVec , fromVec ]
    where toVec : (α × β) → Vec 𝔹 _
          toVec (a , b) = (⇓ a) ++ (⇓ b)

          fromVec : Vec 𝔹 _ → (α × β)
          fromVec bits with splitAt #α bits
          fromVec .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = (⇑ ⇓a) , (⇑ ⇓b)

synthVec : {α : Set} {#α n : ℕ} ⦃ _ : Synth α {#α} ⦄
           → Synth (Vec α n) {n * #α}
synthVec {α} {#α} {n} = Synth[ toVec , fromVec ]
    where toVec : Vec α n → Vec 𝔹 _
          toVec v = v >>= ⇓

          fromVec : Vec 𝔹 _ → Vec α n
          fromVec bits with group n #α bits
          fromVec .(concat grps) | grps , refl = map ⇑ grps

synthVec𝔹 : ∀ {n} → Synth (Vec 𝔹 n)
synthVec𝔹 = synthVec



-- "Smart constructors"
¬ : ℂ 𝔹 𝔹
¬ = Mkℂ Not

synthPair𝔹 : Synth (𝔹 × 𝔹)
synthPair𝔹 = synthPair

∧ : ℂ (𝔹 × 𝔹) 𝔹
∧ = Mkℂ And

∨ : ℂ (𝔹 × 𝔹) 𝔹
∨ = Mkℂ Or

_⟫_ : {α β γ : Set} {#α #β #γ : ℕ}
      ⦃ sα : Synth α {#α} ⦄ ⦃ sβ : Synth β {#β} ⦄ ⦃ sγ : Synth γ {#γ} ⦄
      → ℂ α β {#α} {#β} → ℂ β γ {#β} {#γ} → ℂ α γ {#α} {#γ}
_⟫_ ⦃ sα = sα ⦄ ⦃ sγ = sγ ⦄ (Mkℂ c₁) (Mkℂ c₂) = Mkℂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ >> c₂)

_||_ : {i₁ o₁ i₂ o₂ : Set} {#i₁ #o₁ #i₂ #o₂ : ℕ}
       ⦃ si₁ : Synth i₁ {#i₁} ⦄ ⦃ so₁ : Synth o₁ {#o₁} ⦄ ⦃ si₂ : Synth i₂ {#i₂} ⦄ ⦃ so₂ : Synth o₂ {#o₂} ⦄
       → ℂ i₁ o₁ {#i₁} {#o₁} → ℂ i₂ o₂ {#i₂} {#o₂} →  ℂ (i₁ × i₂) (o₁ × o₂) {#i₁ + #i₂} {#o₁ + #o₂}
_||_ ⦃ si₁ ⦄ ⦃ so₁ ⦄ ⦃ si₂ ⦄ ⦃ so₂ ⦄ (Mkℂ c₁) (Mkℂ c₂) =
    Mkℂ  ⦃ synthPair ⦃ si₁ ⦄ ⦃ si₂ ⦄ ⦄  ⦃ synthPair ⦃ so₁ ⦄ ⦃ so₂ ⦄ ⦄  (c₁ >< c₂)

infixl 7 _||_
infixl 6 _⟫_

testNotNot : ℂ 𝔹 𝔹
testNotNot = ¬ ⟫ ¬

testAndTree : ℂ ((𝔹 × 𝔹) × (𝔹 × 𝔹)) 𝔹
testAndTree =
    let synth𝔹 : Synth ((𝔹 × 𝔹) × (𝔹 × 𝔹))
        synth𝔹 = synthPair
    in ∧ || ∧  ⟫  ∧



allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

core⟦_⟧ : {i o : ℕ} → Coreℂ 𝔹 i o → (Vec 𝔹 i → Vec 𝔹 o)
core⟦ Not ⟧        (x ◁ ε)     = [ not x ]
core⟦ And ⟧        (x ◁ y ◁ ε) = [ x and y ]
core⟦ Or  ⟧        (x ◁ y ◁ ε) = [ x or y ]
core⟦ Plug p ⟧     v           = map (λ o → lookup (p o) v) allFins
core⟦ c₁ >> c₂ ⟧   v           = core⟦ c₂ ⟧ (core⟦ c₁ ⟧ v)
core⟦ _><_ {i₁} c₁ c₂ ⟧ v with splitAt i₁ v
core⟦ c₁ >< c₂ ⟧ .(v₁ ++ v₂) | v₁ , v₂ , refl = core⟦ c₁ ⟧ v₁ ++ core⟦ c₂ ⟧ v₂

⟦_⟧ : {α β : Set} {#α #β : ℕ} → ℂ α β {#α} {#β} → (α → β)
⟦ (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ cc) ⟧ a = ⇑ (core⟦ cc ⟧ (⇓ a))


-- ⑂ : {α : Set} ⦃ sα : Synthesizable α ⦄  →  Circuit α (α × α) ⦃ sα ⦄ ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄
-- ⑂ {α} ⦃ sα ⦄ = Plug {𝔹} {# ⦃ sα ⦄} {# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄} ⑂'
--     where ⑂' : Fin (# ⦃ synthPair ⦃ sα ⦄ ⦃ sα ⦄ ⦄) → Fin (# ⦃ sα ⦄)
--           ⑂' x = {!!}


