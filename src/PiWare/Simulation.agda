module PiWare.Simulation where

open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Vec using (Vec; [_]; splitAt; _++_; map; lookup; _>>=_)
                     renaming (_∷_ to _◁_; [] to ε)
open import Data.Unit using (tt)
open import Data.Fin using (Fin; raise; inject+)
                     renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import PiWare.Wires
open import PiWare.Circuit


wireToIdx : ∀ {w} → ⟬ w ⟭ → Fin (# w)
wireToIdx {↿}     tt        = Fz
wireToIdx {w ⊠ n} (i , w′)  = inject+ (n * # w) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₁ w′) = inject+ (# v) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₂ v′) = raise (# w) (wireToIdx v′)

allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

allWires : ∀ {w} → Vec ⟬ w ⟭ (# w)
allWires {↿}      = [ tt ]
allWires {w ⊠ n} = allFins {suc n}  >>=  λ i → map (λ w′ → (i , w′)) (allWires {w})
allWires {w ⊞ v} = map inj₁ allWires ++ map inj₂ allWires


⟦_⟧[_] : ∀ {α i o} → ℂ α i o → Algℂ α → (Vec α (# i) → Vec α (# o))
⟦ Not    ⟧[ a ] (x ◁ ε)     = [ (Algℂ.¬ a) x ]
⟦ And    ⟧[ a ] (x ◁ y ◁ ε) = [ (Algℂ.∧ a) x y ]
⟦ Or     ⟧[ a ] (x ◁ y ◁ ε) = [ (Algℂ.∨ a) x y ]
⟦ Plug f ⟧[ a ] w           = map (λ o → lookup (wireToIdx (f o)) w) allWires
⟦ c ⟫ d  ⟧[ a ] w           = ⟦ d ⟧[ a ] (⟦ c ⟧[ a ] w)
⟦ _||_ {i₁} c d ⟧[ a ] w with splitAt (# i₁) w
⟦ _||_ {i₁} c d ⟧[ a ] w | w₁ , (w₂ , _) = ⟦ c ⟧[ a ] w₁ ++ ⟦ d ⟧[ a ] w₂
