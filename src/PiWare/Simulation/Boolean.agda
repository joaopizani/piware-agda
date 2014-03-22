module PiWare.Simulation.Boolean where

open import Data.Vec using (Vec)
open import Data.Bool using (Bool; not; _∧_; _∨_)

open import PiWare.Wires using (#_)
open import PiWare.Circuit using (ℂ; Algℂ; algℂ[_,_,_])
open import PiWare.Simulation using (⟦_⟧[_])


boolAlgebra : Algℂ Bool
boolAlgebra = algℂ[ not , _∧_ , _∨_ ]

⟦_⟧b  : ∀ {i o} → ℂ Bool i o → (Vec Bool (# i) → Vec Bool (# o))
⟦ c ⟧b = ⟦ c ⟧[ boolAlgebra ]
