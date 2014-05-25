module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; splitAt; _++_) renaming (_∷_ to _◁_; [] to ε)

import Algebra as Alg
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (Alg.CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)
open import Relation.Binary.PropositionalEquality using (refl)

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


-- Sequential. In: (repeat false)   Out: cycle [false, true]...
sampleToggleXNOR : ℂ* 𝔹 𝔹
sampleToggleXNOR = delayLoopC (sampleXor ⟫ ¬C ⟫ pFork×)


-- MUXES
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-×

-- TODO: booleans for now. How to make it generic?
-- Look at lava: do we need an if-then-else constructor in the BASE CIRCUIT TYPE?
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
sampleMux2to1 : ℂ (𝔹 × (𝔹 × 𝔹)) 𝔹
sampleMux2to1 =
      pFork×
    ⟫ (¬C || pFst ⟫ ∧C)  ||  (pid || pSnd ⟫ ∧C)
    ⟫ ∨C


-- input × load → out
sampleReg : ℂ* (𝔹 × 𝔹) 𝔹
sampleReg = delayLoopC (pALR ⟫ pid || pSwap ⟫ sampleMux2to1 ⟫ pFork×)

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
--     ⟫ pid ||      pFork× || pVecHalfPow  -- needs to become a Combℂ
--     ⟫ pid ||         pIntertwine
--     ⟫ pid || sampleMux n || sampleMux n
--     ⟫                sampleMux2to1

