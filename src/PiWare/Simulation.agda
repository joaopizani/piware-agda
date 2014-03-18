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

--- This should even maybe be in the library...
import Algebra
import Data.Nat.Properties as NatProps
private
    module CSℕ = Algebra.CommutativeSemiring NatProps.commutativeSemiring

--raiseRight : ∀ {m} n → Fin m → Fin (m + n)
--raiseRight {m} n i rewrite CSℕ.+-comm m n = raiseLeft {m} n i
---

wireToIdx : ∀ {w} → ⟬ w ⟭ → Fin (# w)
wireToIdx {↿}     tt        = Fz
wireToIdx {w ⊠ n}   = inject+ (n * # w) (wireToIdx w′) --raise (n * # w) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₁ w′) = inject+ (# v) (wireToIdx w′) -- inject (# v) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₂ v′) = raise (# w) (wireToIdx v′)

allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

allWires : ∀ {w} → Vec ⟬ w ⟭ (# w)
allWires {↿}      = [ tt ]
allWires {w ⊠ n} = allFins {suc n}  >>=  λ i → map (λ w′ → (i , w′)) (allWires {w})
allWires {w ⊞ v} = map inj₁ allWires ++ map inj₂ allWires

⟦_⟧ : ∀ {i o} → ℂ Bool i o → (Vec Bool (# i) → Vec Bool (# o))
⟦ Not    ⟧        (x ◁ ε)     = [ not x ]
⟦ And    ⟧        (x ◁ y ◁ ε) = [ x ∧ y ]
⟦ Or     ⟧        (x ◁ y ◁ ε) = [ x ∨ y ]
⟦ Plug f ⟧        w           = map (λ o → lookup (wireToIdx (f o)) w) allWires
⟦ c ⟫ d  ⟧        w           = ⟦ d ⟧ (⟦ c ⟧ w)
⟦ _||_ {i₁} c d ⟧ w with splitAt (# i₁) w
⟦ _||_ {i₁} c d ⟧ w | w₁ , (w₂ , _) = ⟦ c ⟧ w₁ ++ ⟦ d ⟧ w₂

