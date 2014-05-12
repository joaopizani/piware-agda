module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to 𝔹)

open import PiWare.Synthesizable.Bool
open import PiWare.Circuit 𝔹
open import PiWare.Plugs 𝔹
open import PiWare.Samples using (sampleFullAdder)


private
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
