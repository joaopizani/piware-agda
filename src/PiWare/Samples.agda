module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec)

open import PiWare.Synthesizable.Bool
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

sampleHalfAdder : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)  -- a × b → c × s
sampleHalfAdder =
      pFork×
    ⟫ ∧ || sampleXor

sampleFullAdder : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)  -- (a × b) × cin → cout × s
sampleFullAdder =
      hadd || pid
    ⟫    pALR
    ⟫ pid  || hadd
    ⟫    pARL
    ⟫ ∨    || pid
    where hadd = sampleHalfAdder


private
    ⇓𝕎⇑-×-1 : ⇓𝕎⇑ (𝕎 1 × 𝔹)
    ⇓𝕎⇑-×-𝕎 : {n : ℕ} → ⇓𝕎⇑ (𝕎 (suc n) × 𝕎 (suc n))
    ⇓𝕎⇑-rippleIn : {n : ℕ} → ⇓𝕎⇑ ((𝕎 (suc n) × 𝕎 (suc n)) × 𝔹)
    ⇓𝕎⇑-rippleOut : {n : ℕ} → ⇓𝕎⇑ (𝔹 × 𝕎 (suc n))
    ⇓𝕎⇑-uncons : {α : Set} {#α : ℕ} {n : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (α × Vec α n)
    ⇓𝕎⇑-uncons× : {α : Set} {#α : ℕ} {n : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄
                   → let t = α × Vec α n in ⇓𝕎⇑ (t × t)
    ⇓𝕎⇑-uncons×𝔹 : {n : ℕ} → let t = 𝔹 × Vec 𝔹 n in ⇓𝕎⇑ (t × t)

    ⇓𝕎⇑-×-1           = ⇓𝕎⇑-×
    ⇓𝕎⇑-×-𝕎          = ⇓𝕎⇑-×
    ⇓𝕎⇑-rippleIn      = ⇓𝕎⇑-×
    ⇓𝕎⇑-rippleOut     = ⇓𝕎⇑-×
    ⇓𝕎⇑-uncons ⦃ sα ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec ⦄
    ⇓𝕎⇑-uncons×       = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-uncons ⦄ ⦃ ⇓𝕎⇑-uncons ⦄
    ⇓𝕎⇑-uncons×𝔹     = ⇓𝕎⇑-uncons× {𝔹}

sampleRipple : (n : ℕ) → let n' = suc n in
                         let W = 𝕎 n' in
                         ℂ ((W × W) × 𝔹) (W × 𝔹) {(n' + n') + 1} {n' + 1}
sampleRipple zero = 
      (pSingletonOut || pSingletonOut) || pid
    ⟫           sampleFullAdder
    ⟫   pSingletonIn || pid

sampleRipple (suc m) =
    let
        ⇓𝕎⇑-addBlockIn : ⇓𝕎⇑ ((𝔹 × 𝔹) × (Vec 𝔹 (suc m) × Vec 𝔹 (suc m)))
        ⇓𝕎⇑-addBlockIn = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-Vec ⦄ ⦃ ⇓𝕎⇑-Vec ⦄ ⦄

        ⇓𝕎⇑-bla : ⇓𝕎⇑ (((𝔹 × 𝔹) × (Vec 𝔹 (suc m) × Vec 𝔹 (suc m))) × 𝔹)
        ⇓𝕎⇑-bla = ⇓𝕎⇑-×  ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-Vec ⦄ ⦃ ⇓𝕎⇑-Vec ⦄ ⦄ ⦄  ⦃ ⇓𝕎⇑-𝔹 ⦄

        ⇓𝕎⇑-addBlockOut : ⇓𝕎⇑ ((𝔹 × Vec 𝔹 m) × 𝔹)
        ⇓𝕎⇑-addBlockOut = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-𝔹 ⦄ ⦃ ⇓𝕎⇑-Vec ⦄ ⦄ ⦃ ⇓𝕎⇑-𝔹 ⦄

        addBlock : ℂ (((𝔹 × 𝔹) × (Vec 𝔹 (suc m) × Vec 𝔹 (suc m))) × 𝔹) ((𝔹 × Vec 𝔹 (suc m)) × 𝔹)
                     {(2 + (suc m + suc m)) + 1}  {(1 + suc m) + 1}
        addBlock = {!!}
    in
        (pUncons || pUncons ⟫ pIntertwine) || pid
      ⟫                addBlock
      ⟫              pCons || pid
