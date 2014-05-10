module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec) renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Circuit.Core

open import PiWare.Synthesizable.Bool
open import PiWare.Plugs 𝔹
open import PiWare.Circuit 𝔹


¬C : ℂ 𝔹 𝔹
¬C = Mkℂ Not

∧C : ℂ (𝔹 × 𝔹) 𝔹
∧C = Mkℂ And

∨C : ℂ (𝔹 × 𝔹) 𝔹
∨C = Mkℂ Or


sampleNotNotNot : ℂ 𝔹 𝔹
sampleNotNotNot = ¬C ⟫ ¬C ⟫ ¬C

sampleNand : ℂ (𝔹 × 𝔹) 𝔹
sampleNand = ∧C ⟫ ¬C

sample1And2Or3And4 : ℂ ((𝔹 × 𝔹) × (𝔹 × 𝔹)) 𝔹
sample1And2Or3And4 = (∧C || ∧C) ⟫ ∨C

sampleXor : ℂ (𝔹 × 𝔹) 𝔹
sampleXor =
      pFork×
    ⟫ (¬C || pid ⟫ ∧C)  ||  (pid || ¬C ⟫ ∧C)
    ⟫ ∨C

-- a × b → c × s
sampleHalfAdder : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)
sampleHalfAdder =
      pFork×
    ⟫ ∧C || sampleXor

-- (a × b) × cin → cout × s
sampleFullAdder : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)
sampleFullAdder =
      hadd || pid
    ⟫    pALR
    ⟫ pid  || hadd
    ⟫    pARL
    ⟫ ∨C   || pid
    where hadd = sampleHalfAdder


module RippleCarry where
  ⇓𝕎⇑-𝔹×Vec[𝔹]n                     : {n : ℕ} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
  ⇓𝕎⇑-Vec[𝔹]n×𝔹                     : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × 𝔹)
  ⇓𝕎⇑-𝔹×[Vec[𝔹]n×𝔹]                : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × 𝔹))
  ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×𝔹                 : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × 𝔹)
  ⇓𝕎⇑-Vec[𝔹]n×Vec[𝔹]n               : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × Vec 𝔹 n)
  ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹]n]           : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-𝔹×[𝔹×[Vec[𝔹]n×Vec[𝔹]n]]      : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (𝔹 × (Vec 𝔹 n × Vec 𝔹 n)))
  ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×[𝔹×Vec[𝔹]n]      : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × (𝔹 × Vec 𝔹 n))
  ⇓𝕎⇑-[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]      : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-[𝔹×𝔹]×[𝔹×Vec[𝔹]n×Vec[𝔹]n]   : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-𝔹×[[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × ((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n)))
  ⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[Vec[𝔹]n×Vec[𝔹]n] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×[Vec[𝔹]n×Vec[𝔹]n] : {n : ℕ} → ⇓𝕎⇑ (((𝔹 × 𝔹) × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n))

  ⇓𝕎⇑-𝔹×Vec[𝔹]n                     = ⇓𝕎⇑-×
  ⇓𝕎⇑-Vec[𝔹]n×𝔹                     = ⇓𝕎⇑-×
  ⇓𝕎⇑-𝔹×[Vec[𝔹]n×𝔹]                 = ⇓𝕎⇑-×
  ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×𝔹                 = ⇓𝕎⇑-×
  ⇓𝕎⇑-Vec[𝔹]n×Vec[𝔹]n               = ⇓𝕎⇑-×
  ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹]n]          = ⇓𝕎⇑-×
  ⇓𝕎⇑-𝔹×[𝔹×[Vec[𝔹]n×Vec[𝔹]n]]      = ⇓𝕎⇑-×
  ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×[𝔹×Vec[𝔹]n]      = ⇓𝕎⇑-×
  ⇓𝕎⇑-[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]      = ⇓𝕎⇑-×
  ⇓𝕎⇑-[𝔹×𝔹]×[𝔹×Vec[𝔹]n×Vec[𝔹]n]   = ⇓𝕎⇑-×
  ⇓𝕎⇑-𝔹×[[𝔹×𝔹]×[Vec[𝔹]n×Vec[𝔹]n]] = ⇓𝕎⇑-×
  ⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[Vec[𝔹]n×Vec[𝔹]n] = ⇓𝕎⇑-× 
  ⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×[Vec[𝔹]n×Vec[𝔹]n] = ⇓𝕎⇑-×

  -- cin × a × b → s × cout
  sampleRipple : (n : ℕ) →  let W = Vec 𝔹 n  in  ℂ (𝔹 × W × W) (W × 𝔹)
  sampleRipple zero    = pid || pFst ⟫ pSwap
  sampleRipple (suc m) = pid || (pUncons || pUncons ⟫ pIntertwine)  ⟫  middle  ⟫  pCons || pid
    where middle = pAssoc ⟫ base ⟫ pALR ⟫ recursion ⟫ pARL
            where pAssoc    = pARL ⟫ pARL || pid
                  base      = sampleFullAdder || pid
                  recursion = pid || sampleRipple m

open RippleCarry using (sampleRipple) public


sampleXor' : Coreℂ 𝔹 2 1
sampleXor' =
    (_>>_ {𝔹} {2} {4} {2}
          (pFork' {𝔹} {2} {2})
          ((Not >< pid' {𝔹} {1} >> And)  ><  (pid' {𝔹} {1} >< Not >> And))  )
    >> Or

-- in: repeat false... out: false, true, false, true, false...
sampleToggleXNOR' : Streamℂ 𝔹 1 1
sampleToggleXNOR' = DelayLoop (sampleXNOR' >> pFork' {𝔹} {2} {1})
    where sampleXNOR' : Coreℂ 𝔹 2 1
          sampleXNOR' = sampleXor' >> Not
