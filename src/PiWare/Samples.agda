module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec)

import Algebra as Alg
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (Alg.CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)

open import PiWare.Atom.Bool
open import PiWare.Circuit.Core

open import PiWare.Synthesizable.Bool
open import PiWare.Plugs Atom𝔹
open import PiWare.Circuit Atom𝔹


¬ℂ : ℂ 𝔹 𝔹
¬ℂ = Mkℂ Not

∧ℂ : ℂ (𝔹 × 𝔹) 𝔹
∧ℂ = Mkℂ And 

∨ℂ : ℂ (𝔹 × 𝔹) 𝔹
∨ℂ = Mkℂ Or


¬×3ℂ : ℂ 𝔹 𝔹
¬×3ℂ = ¬ℂ ⟫ ¬ℂ ⟫ ¬ℂ

¬∧ℂ : ℂ (𝔹 × 𝔹) 𝔹
¬∧ℂ = ∧ℂ ⟫ ¬ℂ

⊻ℂ : ℂ (𝔹 × 𝔹) 𝔹
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ

hadd : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)  -- a × b → c × s
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ

fadd : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)  -- (a × b) × cin → co × s
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid


-- Sequential. In: (repeat false)   Out: cycle [false, true]...
toggle : ℂ* 𝔹 𝔹
toggle = delayℂ (⊻ℂ ⟫ ¬ℂ ⟫ pFork×)


-- MUXES
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×[𝔹×𝔹] ⇓𝕎⇑-𝔹×[𝔹×𝔹]

-- TODO: booleans for now. How to make it generic?
-- Look at lava: do we need an if-then-else constructor in the BASE CIRCUIT TYPE?
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
mux2to1 : ℂ (𝔹 × (𝔹 × 𝔹)) 𝔹
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ


-- input × load → out
reg : ℂ* (𝔹 × 𝔹) 𝔹
reg = delayℂ (pSwap || pid  ⟫  pALR  ⟫  (pid || pSwap)  ⟫  mux2to1  ⟫  pFork×)

-- open module ℕ-CS = Alg.CommutativeSemiring ℕ-commSemiring using (+-identity)

-- private
--     ⇓𝕎⇑-A×[I] : {n : ℕ} → let A = Vec 𝔹 n in let I = Vec 𝔹 (2 ^ n) in ⇓𝕎⇑ (A × I)
--     ⇓𝕎⇑-A×[I] = ⇓𝕎⇑-×

--     ⇓𝕎⇑-𝔹×Vec[𝔹]n : {n : ℕ} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
--     ⇓𝕎⇑-𝔹×Vec[𝔹]n = ⇓𝕎⇑-×
    
--     ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×Vec[𝔹][2^n] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × Vec 𝔹 (2 ^ n))
--     ⇓𝕎⇑-[𝔹×Vec[𝔹]n]×Vec[𝔹][2^n] = ⇓𝕎⇑-×

--     ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹][2^n]] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 (2 ^ n)))
--     ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹][2^n]] = ⇓𝕎⇑-×
    
--     ⇓𝕎⇑-[Vec[𝔹]n×Vec[𝔹]n]×[Vec[𝔹][2^n]×Vec[𝔹][2^n]] : {n : ℕ} → ⇓𝕎⇑ ((Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))
--     ⇓𝕎⇑-[Vec[𝔹]n×Vec[𝔹]n]×[Vec[𝔹][2^n]×Vec[𝔹][2^n]] = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄

--     ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹]n]×[Vec[𝔹][2^n]×Vec[𝔹][2^n]] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))
--     ⇓𝕎⇑-𝔹×[Vec[𝔹]n×Vec[𝔹]n]×[Vec[𝔹][2^n]×Vec[𝔹][2^n]] = ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-𝔹 ⦄ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄

-- sampleMux : (n : ℕ) → let A = Vec 𝔹 n  in  ℂ (A × Vec 𝔹 (2 ^ n)) 𝔹 {2 ^ n} {1}
-- sampleMux zero = pSnd ⟫ pSingletonOut
-- sampleMux (suc n) rewrite (proj₂ +-identity) (2 ^ n) =
--       pUncons || pid
--     ⟫        pALR
--     ⟫ pid ||      pFork× || pVecHalfPow
--     ⟫ pid ||         pIntertwine
--     ⟫ pid || sampleMux n || sampleMux n
--     ⟫                sampleMux2to1

