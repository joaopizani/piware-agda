module PiWare.ProofSamples where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; _∧_; _∨_; not)
open import Data.Vec using ([_]) renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Simulation
open import PiWare.Samples


nand : Bool → Bool → Bool
nand a b = not (a ∧ b)

proofNand : ∀ a b → ⟦ sampleNand ⟧ (a ◁ b ◁ ε) ≡ [ nand a b ]
proofNand a b = refl

a-and-b-or-c-and-d : Bool → Bool → Bool → Bool → Bool
a-and-b-or-c-and-d a b c d = (a ∧ b) ∨ (c ∧ d)

proof1And2Or3And4 : ∀ a b c d → ⟦ sample1And2Or3And4 ⟧ (a ◁ b ◁ c ◁ d ◁ ε) ≡ [ a-and-b-or-c-and-d a b c d ]
proof1And2Or3And4 a b c d = refl
