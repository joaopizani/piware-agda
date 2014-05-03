module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)

open import PiWare.Plugs
open import PiWare.Circuit


-- instances that Agda can't figure out, lacking recursive resolution
⇓𝕎⇑-𝔹andPair : ⇓𝕎⇑ (𝔹 × (𝔹 × 𝔹))
⇓𝕎⇑-pairAnd𝔹 : ⇓𝕎⇑ ((𝔹 × 𝔹) × 𝔹)
⇓𝕎⇑-pairPair  : ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × 𝔹))

⇓𝕎⇑-𝔹andPair = ⇓𝕎⇑-×
⇓𝕎⇑-pairAnd𝔹 = ⇓𝕎⇑-×
⇓𝕎⇑-pairPair  = ⇓𝕎⇑-×


sampleNotNotNot : ℂ 𝔹 𝔹
sampleNotNotNot = ¬ ⟫ ¬ ⟫ ¬

sampleNand : ℂ (𝔹 × 𝔹) 𝔹
sampleNand = ∧ ⟫ ¬

sample1And2Or3And4 : ℂ ((𝔹 × 𝔹) × (𝔹 × 𝔹)) 𝔹
sample1And2Or3And4 = (∧ || ∧) ⟫ ∨

sampleXor : ℂ (𝔹 × 𝔹) 𝔹
sampleXor =
      pFork×
    ⟫ (¬ || pid ⟫ ∧)  ||  (pid || ¬ ⟫ ∧)
    ⟫ ∨

sampleHalfAdder : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)
sampleHalfAdder =
      pFork×
    ⟫ ∧ || sampleXor

sampleFullAdder : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)
sampleFullAdder =
      hadd || pid
    ⟫    pALR
    ⟫ pid  || hadd
    ⟫    pARL
    ⟫ ∨    || pid
    where hadd = sampleHalfAdder


{-
sampleRipple : (n : ℕ) → ℂ Bool (1 + (n + n)) (1 + n)
sampleRipple zero = 
                    pSwap
    ⟫ (pSingletonOut || pSingletonOut) || pid
    ⟫           sampleFullAdder
    ⟫   pSingletonIn || pid
sampleRipple (suc m) = 
      pid || ((pUncons || pUncons) ⟫ pIntertwine)
    ⟫                addBlock
    ⟫              pCons || pid
    where
        addBlock : ℂ Bool  (1 + (2 + (m + m)))  (1 + (1 + m))
        addBlock = {!!}
-}
