module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec) renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Synthesizable.Bool
open import PiWare.Plugs
open import PiWare.Circuit



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


⇓𝕎⇑-Vec[𝔹]1×Vec[𝔹]1 : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × Vec 𝔹 n)
⇓𝕎⇑-Vec[𝔹]1×Vec[𝔹]1 = ⇓𝕎⇑-Vec[a]×b

⇓𝕎⇑-[Vec[𝔹]1×Vec[𝔹]1]×𝔹 : {n : ℕ} → ⇓𝕎⇑ ((Vec 𝔹 n × Vec 𝔹 n) × 𝔹)
⇓𝕎⇑-[Vec[𝔹]1×Vec[𝔹]1]×𝔹 = ⇓𝕎⇑-×

⇓𝕎⇑-Vec[𝔹]n×𝔹 : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × 𝔹)
⇓𝕎⇑-Vec[𝔹]n×𝔹 = ⇓𝕎⇑-×

⇓𝕎⇑-𝔹×Vec[𝔹]n : {n : ℕ} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
⇓𝕎⇑-𝔹×Vec[𝔹]n = ⇓𝕎⇑-×

⇓𝕎⇑-[𝔹×Vec[𝔹]n]×[𝔹×Vec[𝔹]n] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × (𝔹 × Vec 𝔹 n))
⇓𝕎⇑-[𝔹×Vec[𝔹]n]×[𝔹×Vec[𝔹]n] = ⇓𝕎⇑-×

⇓𝕎⇑-[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n))
⇓𝕎⇑-[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n] = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄

⇓𝕎⇑-[[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]]×𝔹 : {n : ℕ} → ⇓𝕎⇑ (((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n)) × 𝔹)
⇓𝕎⇑-[[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]]×𝔹 = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄ ⦃ ⇓𝕎⇑-𝔹 ⦄

⇓𝕎⇑-[𝔹×Vec[𝔹]n]×𝔹 : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × 𝔹)
⇓𝕎⇑-[𝔹×Vec[𝔹]n]×𝔹 = ⇓𝕎⇑-×

-- TODO
postulate addBlock : {m : ℕ} → ℂ (((𝔹 × 𝔹) × (Vec 𝔹 m × Vec 𝔹 m)) × 𝔹) ((𝔹 × Vec 𝔹 m) × 𝔹) {(2 + (m * 1 + m * 1)) + 1}  {(1 + m * 1) + 1}

sampleRipple : (n : ℕ) → let W = Vec 𝔹 n in ℂ ((W × W) × 𝔹) (W × 𝔹) {(n * 1 + n * 1) + 1} {n * 1 + 1}
sampleRipple zero    = pFst || pid
sampleRipple (suc m) = (pUncons || pUncons ⟫ pIntertwine) || pid  ⟫  addBlock  ⟫  pCons || pid
