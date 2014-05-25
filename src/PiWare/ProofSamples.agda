module PiWare.ProofSamples where

open import Function using (_$_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false)
                      renaming (Bool to 𝔹)

open import Data.Stream using (Stream; repeat; _≈_; zipWith; _∷_; take; head; tail) renaming (map to smap)
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
toggle = ⟦ sampleToggleXNOR ⟧* (repeat false)


-- reg seems to be working (input × load → out)
rhold = take 7 (⟦ sampleReg ⟧* $ zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false)) (true ∷ ♯ repeat false) )
rload = take 7 (⟦ sampleReg ⟧* $ zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false)) (false ∷ ♯ (true ∷ ♯ repeat false)) )


-- head is always false
proofRegHeadFalse : ∀ {loads ins} → head (⟦ sampleReg ⟧* (zipWith _,_ loads ins)) ≡ false
proofRegHeadFalse = refl


-- this works...
proofRepeatFalse' : tail (repeat false) ≈ repeat false
proofRepeatFalse' = refl ∷ ♯ proofRepeatFalse'

-- only by using the tail proof
proofRepeatFalse : repeat false ≈ false ∷ ♯ repeat false
proofRepeatFalse = refl ∷ ♯ proofRepeatFalse'


-- when ¬load, then tail of output is repeat head of input

-- now with the register: first the tail
proofRegNeverLoadHardcoded' : tail (⟦ sampleReg ⟧* (repeat (true , false))) ≈ repeat false
proofRegNeverLoadHardcoded' = refl ∷ ♯ proofRegNeverLoadHardcoded'

-- then the case including the head
proofRegNeverLoadHardcoded : ⟦ sampleReg ⟧* (repeat (true , false)) ≈ false ∷ ♯ repeat false
proofRegNeverLoadHardcoded = refl ∷ ♯ proofRegNeverLoadHardcoded'

-- trying to be a bit more general now: first the tail
proofRegNeverLoad' : ∀ xs → tail (⟦ sampleReg ⟧* $ zipWith _,_ xs (repeat false) ) ≈ repeat false
proofRegNeverLoad' (x ∷ xs) = refl ∷ ♯ proofRegNeverLoad' (♭ xs)

-- then the case including the head...
proofRegNeverLoad : ∀ xs → ⟦ sampleReg ⟧* (zipWith _,_ xs (repeat false)) ≈ false ∷ ♯ repeat false
proofRegNeverLoad xs = refl ∷ ♯ proofRegNeverLoad' xs


-- when load, tail of output is input
-- first hardcoded
proofRegAlwaysLoadHardcoded' : tail (⟦ sampleReg ⟧* (repeat (true , true))) ≈ repeat true
proofRegAlwaysLoadHardcoded' = refl ∷ ♯ proofRegAlwaysLoadHardcoded'

proofRegAlwaysLoadHardcoded : ⟦ sampleReg ⟧* (repeat (true , true)) ≈ false ∷ ♯ repeat true
proofRegAlwaysLoadHardcoded = refl ∷ ♯ proofRegAlwaysLoadHardcoded'

proofRegAlwaysLoad' : ∀ xs → tail (⟦ sampleReg ⟧* (zipWith _,_ xs (repeat true))) ≈ xs
proofRegAlwaysLoad' (true  ∷ xs) = refl ∷ ♯ {!proofRegAlwaysLoad' (♭ xs)!}
proofRegAlwaysLoad' (false ∷ xs) = refl ∷ ♯ proofRegAlwaysLoad' (♭ xs)  -- "coincidence"?

proofRegAlwaysLoad : ∀ xs → ⟦ sampleReg ⟧* (zipWith _,_ xs (repeat true)) ≈ false ∷ ♯ xs
proofRegAlwaysLoad xs = refl ∷ ♯ proofRegAlwaysLoad' xs
