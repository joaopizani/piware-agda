module PiWare.Wires where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; _++_; map; [_]; _>>=_) renaming ([] to ε; _∷_ to _◁_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin; inject+; raise) renaming (zero to Fz; suc to Fs)


-- Elements of this type describe the *structure* of circuit IO ports
data Wires : Set where
    ↿    : Wires
    _⊠_ : Wires → (n : ℕ) → Wires  -- a vector with indices [0,n]
    _⊞_ : Wires → Wires    → Wires

infixl 9 _⊠_
infixl 8 _⊞_


-- The size of a circuit's input (or output) interface
#_ : Wires → ℕ
# ↿        = 1
# (w ⊠ n) = suc n * (# w)
# (w ⊞ v) = (# w) + (# v)

-- Mapping elements of Wires to Agda types (universe construction)
⟬_⟭ : Wires → Set
⟬ ↿ ⟭      = ⊤
⟬ w ⊠ n ⟭ = Fin (suc n) × ⟬ w ⟭  -- An index, together with an element
⟬ w ⊞ v ⟭ = ⟬ w ⟭ ⊎ ⟬ v ⟭

-- Given an element of the type encoded by w, flattens it into a natural-coded index
wireToIdx : ∀ {w} → ⟬ w ⟭ → Fin (# w)
wireToIdx {↿}     tt        = Fz
wireToIdx {w ⊠ n} (i , w′)  = inject+ (n * # w) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₁ w′) = inject+ (# v) (wireToIdx w′)
wireToIdx {w ⊞ v} (inj₂ v′) = raise (# w) (wireToIdx v′)

-- Gives a vector with all the n elements of (Fin n), in increasing order
allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

-- Gives a vector with all elements of the type encoded by w
allWires : ∀ {w} → Vec ⟬ w ⟭ (# w)
allWires {↿}      = [ tt ]
allWires {w ⊠ n} = allFins {suc n}  >>=  λ i → map (λ w′ → (i , w′)) (allWires {w})
allWires {w ⊞ v} = map inj₁ allWires ++ map inj₂ allWires
