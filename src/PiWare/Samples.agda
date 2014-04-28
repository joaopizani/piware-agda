module PiWare.Samples where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool)

open import PiWare.Circuit using (ℂ; Not; And; Or; _⟫_; _||_; _><_)
open import PiWare.Plugs
    using (pid; fork2; pALR; pARL; pHead; pCons; pUncons; pIntertwine)


sampleNotNotNot : ℂ Bool 1 1
sampleNotNotNot = Not ⟫ Not ⟫ Not

sampleNand : ℂ Bool 2 1
sampleNand = And ⟫ Not

sample1And2Or3And4 : ℂ Bool 4 1
sample1And2Or3And4 = And || And ⟫ Or

sampleXor : ℂ Bool 2 1
sampleXor =
    fork2 ⟫    (Not >< pid  ⟫ And)
            || (pid >< Not  ⟫ And)  ⟫ Or

sampleHalfAdder : ℂ Bool 2 2
sampleHalfAdder =
    fork2 ⟫    And
            || sampleXor

sampleFullAdder : ℂ Bool 3 2
sampleFullAdder =
      hadd           || pid
    ⟫ pid {Bool} {1} || hadd
    ⟫ Or             || pid
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
