module PiWare.ProofSamples where

open import Data.Product using (_×_; _,_)
open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to 𝔹)

open import Data.Stream using (Stream; repeat; _≈_; zipWith; _∷_; take; head; tail)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Coinduction

open import PiWare.Samples
open import PiWare.Simulation


proofNand : ∀ a b → ⟦ sampleNand ⟧ (a , b) ≡ not (a ∧ b)
proofNand a b = refl


proof1And2Or3And4 : ∀ a b c d → ⟦ sample1And2Or3And4 ⟧ ((a , b) , (c , d)) ≡ (a ∧ b) ∨ (c ∧ d)
proof1And2Or3And4 a b c d = refl


booleanXorEquiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
booleanXorEquiv true  b     = refl
booleanXorEquiv false true  = refl
booleanXorEquiv false false = refl

proofXor : ∀ a b → ⟦ sampleXor ⟧ (a , b) ≡ a xor b
proofXor = booleanXorEquiv


halfAddSpec : 𝔹 → 𝔹 → (𝔹 × 𝔹)
halfAddSpec a b = (a ∧ b) , (a xor b)

-- TODO: better proof here, using proofXor, proofAnd and some "parallel proof combinator"
proofHalfAddBool : ∀ a b → ⟦ sampleHalfAdder ⟧ (a , b) ≡ halfAddSpec a b
proofHalfAddBool a b = cong (_,_ (a ∧ b)) (booleanXorEquiv a b)


-- TODO: make fullAddSpec in terms of halfAddSpec?
fullAddTable : 𝔹 → 𝔹 → 𝔹 → (𝔹 × 𝔹)
fullAddTable false false false = false , false
fullAddTable false false true  = false , true
fullAddTable false true  false = false , true
fullAddTable false true  true  = true  , false
fullAddTable true  false false = false , true
fullAddTable true  false true  = true  , false
fullAddTable true  true  false = true  , false
fullAddTable true  true  true  = true  , true

proofFullAdderBool : ∀ a b c → ⟦ sampleFullAdder ⟧ ((a , b) , c) ≡ fullAddTable a b c
proofFullAdderBool true  true  true  = refl
proofFullAdderBool true  true  false = refl
proofFullAdderBool true  false true  = refl
proofFullAdderBool true  false false = refl
proofFullAdderBool false true  true  = refl
proofFullAdderBool false true  false = refl
proofFullAdderBool false false true  = refl
proofFullAdderBool false false false = refl

toggle : Stream 𝔹
toggle = ⟦ sampleToggle ⟧* (repeat false)

regFirstFalse : Stream 𝔹
regFirstFalse = ⟦ sampleReg ⟧* (repeat (true , true))


-- head is always false
-- when ¬load, then tail of output is repeat head of input
-- when load, tail of output is input

proofRegHeadFalse : ∀ {loads ins} → head (⟦ sampleReg ⟧* (zipWith _,_ loads ins)) ≡ false
proofRegHeadFalse = refl

proofRegTailNeverLoad' : tail (⟦ sampleReg ⟧* (repeat (false , true))) ≈ repeat false
proofRegTailNeverLoad' = refl ∷ ♯ proofRegTailNeverLoad'

-- TODO: why doesn't it work?
proofRegTailNeverLoad : ∀ xs → tail (⟦ sampleReg ⟧* (zipWith _,_ (repeat false) xs)) ≈ xs
proofRegTailNeverLoad xs = {!!}


proofTailFalse : tail (repeat false) ≈ repeat false
proofTailFalse = refl ∷ ♯ proofTailFalse

proofRepeatFalse : repeat false ≈ false ∷ ♯ repeat false
proofRepeatFalse = refl ∷ ♯ proofTailFalse

-- proofRepeatFalse : repeat false ≈ false ∷ ♯ repeat false
-- proofRepeatFalse = refl ∷ {!♯ proofRepeatFalse!}
