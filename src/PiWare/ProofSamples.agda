module PiWare.ProofSamples where

open import Data.Product using (_×_; _,_)
open import Data.Bool using (not; _xor_; true; false)
                      renaming (Bool to 𝔹; _∧_ to _and_; _∨_ to _or_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Samples
open import PiWare.Simulation


proofNand : ∀ a b → ⟦ sampleNand ⟧ (a , b) ≡ not (a and b)
proofNand a b = refl

proof1And2Or3And4 : ∀ a b c d → ⟦ sample1And2Or3And4 ⟧ ((a , b) , (c , d)) ≡ (a and b) or (c and d)
proof1And2Or3And4 a b c d = refl

booleanXorEquiv : ∀ a b → (not a and b) or (a and not b) ≡ (a xor b)
booleanXorEquiv true  b     = refl
booleanXorEquiv false true  = refl
booleanXorEquiv false false = refl

proofXor : ∀ a b → ⟦ sampleXor ⟧ (a , b) ≡ a xor b
proofXor = booleanXorEquiv

halfAddSpec : 𝔹 → 𝔹 → (𝔹 × 𝔹)
halfAddSpec a b = (a and b) , (a xor b)

proofHalfAddBool : ∀ a b → ⟦ sampleHalfAdder ⟧ (a , b) ≡ halfAddSpec a b
proofHalfAddBool a b = cong (_,_ (a and b)) (booleanXorEquiv a b)

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
