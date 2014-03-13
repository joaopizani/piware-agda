module PiWare.Simulation where

open import Data.Product using (_,_)
open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Vec using (Vec; [_]; splitAt; _++_)
                     renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Wires
open import PiWare.Circuit


⟦_⟧ : ∀ {i o} → ℂ Bool i o → (Vec Bool (# i) → Vec Bool (# o))
⟦ Not ⟧    (x ◁ ε) = [ not x ] 
⟦ And ⟧    (x ◁ y ◁ ε) = [ x ∧ y ]
⟦ Or ⟧     (x ◁ y ◁ ε) = [ x ∨ y ]
⟦ Plug f ⟧ w = {!!}
⟦ c ⟫ d ⟧  w = ⟦ d ⟧ (⟦ c ⟧ w)
⟦ _||_ {i₁} c d ⟧ w with splitAt (# i₁) w
⟦ _||_ {i₁} c d ⟧ w | w₁ , (w₂ , _) = ⟦ c ⟧ w₁ ++ ⟦ d ⟧ w₂
