module PiWare.Samples where

open import Data.Bool using (Bool)
open import PiWare.Wires
open import PiWare.Circuit
open import PiWare.Plugs


sampleNotNotNot : ℂ Bool ↿ ↿
sampleNotNotNot = Not ⟫ Not ⟫ Not

sampleNand : ℂ Bool (↿ ⊞ ↿) ↿
sampleNand = And ⟫ Not

sample1And2Or3And4 : ℂ Bool ((↿ ⊞ ↿) ⊞ (↿ ⊞ ↿)) ↿
sample1And2Or3And4 = (And || And) ⟫ Or

sampleXor : ℂ Bool (↿ ⊞ ↿) ↿
sampleXor =
    fork2 ⟫    (Not || pid  ⟫ And)
            || (pid || Not  ⟫ And)  ⟫ Or

sampleHalfAdder : ℂ Bool (↿ ⊞ ↿) (↿ ⊞ ↿)
sampleHalfAdder =
    fork2 ⟫    sampleXor
            || And
