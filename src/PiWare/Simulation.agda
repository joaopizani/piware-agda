module PiWare.Simulation where

open import Data.Product using (_,_)
open import Data.Vec using (Vec; [_]; splitAt; _++_; map; lookup)
                     renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Wires using (#_; allWires; wireToIdx)
open import PiWare.Circuit using (ℂ; Algℂ; Not; And; Or; Plug; _⟫_; _||_)


-- Evaluation (simulation) of a circuit, given an algebra
⟦_⟧[_] : ∀ {α i o} → ℂ α i o → Algℂ α → (Vec α (# i) → Vec α (# o))
⟦ Not    ⟧[ a ] (x ◁ ε)     = [ (Algℂ.¬ a) x ]
⟦ And    ⟧[ a ] (x ◁ y ◁ ε) = [ (Algℂ.∧ a) x y ]
⟦ Or     ⟧[ a ] (x ◁ y ◁ ε) = [ (Algℂ.∨ a) x y ]
⟦ Plug f ⟧[ a ] w           = map (λ o → lookup (wireToIdx (f o)) w) allWires
⟦ c ⟫ d  ⟧[ a ] w           = ⟦ d ⟧[ a ] (⟦ c ⟧[ a ] w)
⟦ _||_ {i₁} c d ⟧[ a ] w with splitAt (# i₁) w
⟦ _||_ {i₁} c d ⟧[ a ] w | w₁ , (w₂ , _) = ⟦ c ⟧[ a ] w₁ ++ ⟦ d ⟧[ a ] w₂
