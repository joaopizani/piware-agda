module PiWare.Simulation.Boolean where

open import Data.Vec using (Vec)
open import Data.Bool using (Bool; not; _∧_; _∨_)

open import PiWare.Wires
open import PiWare.Circuit
open import PiWare.Simulation


boolAlgebra : Algℂ Bool
boolAlgebra = algℂ[ not , _∧_ , _∨_ ]

⟦_⟧b : ∀ {i o} → ℂ Bool i o → (Vec Bool (# i) → Vec Bool (# o))
⟦ c ⟧b = ⟦ c ⟧[ boolAlgebra ]
