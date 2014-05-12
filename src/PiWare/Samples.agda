module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec) renaming (_∷_ to _◁_; [] to ε)

open import Algebra using () renaming (CommutativeSemiring to CS)
open import Data.Nat.Properties using () renaming (commutativeSemiring to NatCommSemiring)
open import Algebra.Operations (CS.semiring NatCommSemiring) using (_^_)

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




sampleXor' : Combℂ 𝔹 2 1
sampleXor' =
       (pFork' {𝔹} {2} {2})
    >> ((Not >< pid' {𝔹} {1} >> And)  ><  (pid' {𝔹} {1} >< Not >> And))
    >> Or

-- in: repeat false... out: false, true, false, true, false...
sampleToggleXNOR' : Coreℂ 𝔹 1 1
sampleToggleXNOR' = Delayed (sampleXNOR' >> pFork' {𝔹} {2} {1})
    where sampleXNOR' : Combℂ 𝔹 2 1
          sampleXNOR' = sampleXor' >> Not
