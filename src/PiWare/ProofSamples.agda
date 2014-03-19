module PiWare.ProofSamples where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; _xor_)
open import Data.Vec using (Vec; [_]) renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Simulation
open import PiWare.Samples


nand : Bool → Bool → Bool
nand a b = not (a ∧ b)

proofNand : ∀ a b → ⟦ sampleNand ⟧b (a ◁ b ◁ ε) ≡ [ nand a b ]
proofNand a b = refl

a-and-b-or-c-and-d : Bool → Bool → Bool → Bool → Bool
a-and-b-or-c-and-d a b c d = (a ∧ b) ∨ (c ∧ d)

proof1And2Or3And4 : ∀ a b c d → ⟦ sample1And2Or3And4 ⟧b (a ◁ b ◁ c ◁ d ◁ ε) ≡ [ a-and-b-or-c-and-d a b c d ]
proof1And2Or3And4 a b c d = refl

booleanXorEquiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
booleanXorEquiv true  true  = refl
booleanXorEquiv true  false = refl
booleanXorEquiv false true  = refl
booleanXorEquiv false false = refl

proofXor : ∀ a b -> ⟦ sampleXor ⟧b (a ◁ b ◁ ε) ≡ [ a xor b ]
proofXor a b = cong [_] (booleanXorEquiv a b)

halfAddSpec : Bool → Bool → Vec Bool 2
halfAddSpec a b = (a ∧ b) ◁ (a xor b) ◁ ε

proofHalfAddBool : ∀ a b → ⟦ sampleHalfAdder ⟧b (a ◁ b ◁ ε) ≡ halfAddSpec a b
proofHalfAddBool a b = cong (λ s → (a ∧ b) ◁ s ◁ ε) (booleanXorEquiv a b)

fullAddSpec : Bool → Bool → Bool → Vec Bool 2
fullAddSpec false false false = false ◁ false ◁ ε
fullAddSpec false false true  = false ◁ true  ◁ ε
fullAddSpec false true  false = false ◁ true  ◁ ε
fullAddSpec false true  true  = true  ◁ false ◁ ε
fullAddSpec true  false false = false ◁ true  ◁ ε
fullAddSpec true  false true  = true  ◁ false ◁ ε
fullAddSpec true  true  false = true  ◁ false ◁ ε
fullAddSpec true  true  true  = true  ◁ true  ◁ ε

proofFullAdderBool : ∀ a b c → ⟦ sampleFullAdder ⟧b (a ◁ b ◁ c ◁ ε) ≡ fullAddSpec a b c
proofFullAdderBool true  true  true  = refl
proofFullAdderBool true  true  false = refl
proofFullAdderBool true  false true  = refl
proofFullAdderBool true  false false = refl
proofFullAdderBool false true  true  = refl
proofFullAdderBool false true  false = refl
proofFullAdderBool false false true  = refl
proofFullAdderBool false false false = refl
