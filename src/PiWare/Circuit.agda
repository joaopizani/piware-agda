module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_; _*_; zero; suc)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (not) renaming (Bool to 𝔹; _∧_ to _and_; _∨_ to _or_)
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

infixr 5 _><_
infixl 4 _>>_

-- "Algebra" for evaluating a circuit, closely related to the ℂ type itself.
-- Each field of the algebra corresponds to a "fundamental" constructor of ℂ
record Algℂ (α : Set) : Set where
   constructor algℂ[_,_,_]
   field
       ¬ : α → α
       ∧ : α → α → α
       ∨ : α → α → α



-- Binary words
𝕎 : ℕ → Set
𝕎 n = Vec 𝔹 n

-- Provides a mapping between "high-level" metalanguage types and vectors of bits
record ⇓𝕎⇑ (α : Set) {#α : ℕ} : Set where
    constructor ⇓𝕎⇑[_,_]
    field
        ⇓ : α → Vec 𝔹 #α  -- to bit vectors
        ⇑ : Vec 𝔹 #α → α  -- from bit vectors

open ⇓𝕎⇑ {{...}}

⇓𝕎⇑-× : {α β : Set} {#α #β : ℕ} ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ ⦃ _ : ⇓𝕎⇑ β {#β} ⦄ → ⇓𝕎⇑ (α × β) {#α + #β}
⇓𝕎⇑-× {α} {β} {#α} = ⇓𝕎⇑[ down , up ]
    where down : (α × β) → Vec 𝔹 _
          down (a , b) = (⇓ a) ++ (⇓ b)

          up : Vec 𝔹 _ → (α × β)
          up bits with splitAt #α bits
          up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = (⇑ ⇓a) , (⇑ ⇓b)

⇓𝕎⇑-Vec : {α : Set} {#α n : ℕ} ⦃ _ : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (Vec α n) {n * #α}
⇓𝕎⇑-Vec {α} {#α} {n} = ⇓𝕎⇑[ down , up ]
    where down : Vec α n → 𝕎 _
          down v = v >>= ⇓

          up : 𝕎 _ → Vec α n
          up bits with group n #α bits
          up .(concat grps) | grps , refl = map ⇑ grps


⇓𝕎⇑-𝔹 : ⇓𝕎⇑ 𝔹
⇓𝕎⇑-𝔹 = ⇓𝕎⇑[ down , up ]
    where down : 𝔹 → 𝕎 _
          down b = [ b ]
          
          up : 𝕎 _ → 𝔹
          up (bit ◁ ε) = bit

⇓𝕎⇑-Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n)
⇓𝕎⇑-Vec𝔹 = ⇓𝕎⇑-Vec



-- "High-level" circuit datatype, packing the synthesis information
data ℂ (i o : Set) {#i #o : ℕ} : Set where Mkℂ : ⦃ _ : ⇓𝕎⇑ i {#i} ⦄ ⦃ _ : ⇓𝕎⇑ o {#o} ⦄ → Coreℂ 𝔹 #i #o → ℂ i o {#i} {#o}

-- "Smart constructors"
¬ : ℂ 𝔹 𝔹
¬ = Mkℂ Not

⇓𝕎⇑-𝔹×𝔹 : ⇓𝕎⇑ (𝔹 × 𝔹)
⇓𝕎⇑-𝔹×𝔹 = ⇓𝕎⇑-×

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

