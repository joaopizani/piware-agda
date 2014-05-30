module PiWare.ProofSamples where

open import Function using (_$_)
open import Data.Product using (_×_; _,_) renaming (map to pmap)
open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to 𝔹)

open import Data.Stream using (Stream; repeat; _≈_; zipWith; _∷_; take; head; tail) renaming (map to smap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Coinduction

open import PiWare.Samples
open import PiWare.Simulation


proofAnd : ∀ a b → ⟦ ∧ℂ ⟧ (a , b) ≡ a ∧ b
proofAnd a b = refl


proofNand : ∀ a b → ⟦ ¬∧ℂ ⟧ (a , b) ≡ not (a ∧ b)
proofNand a b = refl


xorEquiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
xorEquiv true  b     = refl
xorEquiv false true  = refl
xorEquiv false false = refl

proofXor : ∀ a b → ⟦ ⊻ℂ ⟧ (a , b) ≡ a xor b
proofXor = xorEquiv


-- proof "combinators"
_⟫≡_ : ∀ {c₁ c₂ f₁ f₂ x y} → (⟦ c₁ ⟧ x ≡ f₁ x) → (⟦ c₂ ⟧ y ≡ f₂ y) → ⟦ c₁ ⟫ c₂ ⟧ x ≡ (f₂ ∘ f₁) x
p₁ ⟫≡ p₂ = ?

_|≡_ : ∀ {c₁ c₂ f₁ f₂ x y} → (⟦ c₁ ⟧ x ≡ f₁ x) → (⟦ c₂ ⟧ y ≡ f₂ y) → ⟦ c₁ || c₂ ⟧ (x , y) ≡ pmap f₁ f₂ (x , y)
p₁ |≡ p₂ rewrite p₁ | p₂ = refl


haddSpec : 𝔹 → 𝔹 → (𝔹 × 𝔹)
haddSpec a b = (a ∧ b) , (a xor b)

proofHaddBool' : ∀ {a b} → ⟦ hadd ⟧ (a , b) ≡ haddSpec a b
proofHaddBool' = proofAnd |≡ proofXor


-- TODO: better proof here, using proofXor, proofAnd and some "parallel proof combinator"
proofHaddBool : ∀ a b → ⟦ hadd ⟧ (a , b) ≡ haddSpec a b
proofHaddBool a b = cong (_,_ (a ∧ b)) (xorEquiv a b)


-- TODO: make fullAddSpec in terms of halfAddSpec?
faddSpec : 𝔹 → 𝔹 → 𝔹 → (𝔹 × 𝔹)
faddSpec false false false = false , false
faddSpec false false true  = false , true
faddSpec false true  false = false , true
faddSpec false true  true  = true  , false
faddSpec true  false false = false , true
faddSpec true  false true  = true  , false
faddSpec true  true  false = true  , false
faddSpec true  true  true  = true  , true

proofFaddBool : ∀ a b c → ⟦ fadd ⟧ ((a , b) , c) ≡ faddSpec a b c
proofFaddBool true  true  true  = refl
proofFaddBool true  true  false = refl
proofFaddBool true  false true  = refl
proofFaddBool true  false false = refl
proofFaddBool false true  true  = refl
proofFaddBool false true  false = refl
proofFaddBool false false true  = refl
proofFaddBool false false false = refl


toggle : Stream 𝔹
toggle = ⟦ sampleToggle ⟧* (repeat false)


-- reg seems to be working (input × load → out)
rhold = take 7 (⟦ reg ⟧* $ zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false)) (true ∷ ♯ repeat false) )
rload = take 7 (⟦ reg ⟧* $ zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false)) (false ∷ ♯ (true ∷ ♯ repeat false)) )


-- head is always false
proofRegHeadFalse : ∀ {loads ins} → head (⟦ reg ⟧* (zipWith _,_ loads ins)) ≡ false
proofRegHeadFalse = refl


-- this works...
proofRepeatFalse' : tail (repeat false) ≈ repeat false
proofRepeatFalse' = refl ∷ ♯ proofRepeatFalse'

-- only by using the tail proof
proofRepeatFalse : repeat false ≈ false ∷ ♯ repeat false
proofRepeatFalse = refl ∷ ♯ proofRepeatFalse'


-- when ¬load, then tail of output is repeat head of input

-- now with the register: first the tail
proofRegNeverLoadHardcoded' : tail (⟦ reg ⟧* (repeat (true , false))) ≈ repeat false
proofRegNeverLoadHardcoded' = refl ∷ ♯ proofRegNeverLoadHardcoded'

-- then the case including the head
proofRegNeverLoadHardcoded : ⟦ reg ⟧* (repeat (true , false)) ≈ false ∷ ♯ repeat false
proofRegNeverLoadHardcoded = refl ∷ ♯ proofRegNeverLoadHardcoded'

-- trying to be a bit more general now: first the tail
proofRegNeverLoad' : ∀ xs → tail (⟦ reg ⟧* $ zipWith _,_ xs (repeat false) ) ≈ repeat false
proofRegNeverLoad' (x ∷ xs) = refl ∷ ♯ proofRegNeverLoad' (♭ xs)

-- then the case including the head...
proofRegNeverLoad : ∀ xs → ⟦ reg ⟧* (zipWith _,_ xs (repeat false)) ≈ false ∷ ♯ repeat false
proofRegNeverLoad xs = refl ∷ ♯ proofRegNeverLoad' xs


-- when load, tail of output is input
-- first hardcoded
proofRegAlwaysLoadHardcoded' : tail (⟦ reg ⟧* (repeat (true , true))) ≈ repeat true
proofRegAlwaysLoadHardcoded' = refl ∷ ♯ proofRegAlwaysLoadHardcoded'

proofRegAlwaysLoadHardcoded : ⟦ reg ⟧* (repeat (true , true)) ≈ false ∷ ♯ repeat true
proofRegAlwaysLoadHardcoded = refl ∷ ♯ proofRegAlwaysLoadHardcoded'

proofRegAlwaysLoad' : ∀ xs → tail (⟦ reg ⟧* (zipWith _,_ xs (repeat true))) ≈ xs
proofRegAlwaysLoad' (true  ∷ xs) = refl ∷ ♯ {!proofRegAlwaysLoad' (♭ xs)!}
proofRegAlwaysLoad' (false ∷ xs) = refl ∷ ♯ proofRegAlwaysLoad' (♭ xs)  -- "coincidence"?

proofRegAlwaysLoad : ∀ xs → ⟦ reg ⟧* (zipWith _,_ xs (repeat true)) ≈ false ∷ ♯ xs
proofRegAlwaysLoad xs = refl ∷ ♯ proofRegAlwaysLoad' xs
