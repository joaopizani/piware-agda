module PiWare.Samples where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)

open import PiWare.Wires using (↿; _⊞_; _⊠_)
open import PiWare.Circuit using (ℂ; Not; And; Or; _⟫_; _||_)
open import PiWare.Plugs
    using ( pid; fork2; pALR; pARL; pHead; pSingletonOut
          ; pSingletonIn; pCons; pUncons; pIntertwine )


sampleNotNotNot : ℂ Bool ↿ ↿
sampleNotNotNot = Not ⟫ Not ⟫ Not

sampleNand : ℂ Bool (↿ ⊞ ↿) ↿
sampleNand = And ⟫ Not

sample1And2Or3And4 : ℂ Bool ((↿ ⊞ ↿) ⊞ (↿ ⊞ ↿)) ↿
sample1And2Or3And4 = And || And ⟫ Or

sampleXor : ℂ Bool (↿ ⊞ ↿) ↿
sampleXor =
    fork2 ⟫    (Not || pid  ⟫ And)
            || (pid || Not  ⟫ And)  ⟫ Or

sampleHalfAdder : ℂ Bool (↿ ⊞ ↿) (↿ ⊞ ↿)
sampleHalfAdder =
    fork2 ⟫    And
            || sampleXor

sampleFullAdder : ℂ Bool ((↿ ⊞ ↿) ⊞ ↿) (↿ ⊞ ↿)
sampleFullAdder =
      hadd || pid
    ⟫     pALR
    ⟫ pid  || hadd
    ⟫     pARL
    ⟫ Or   || pid
    where hadd = sampleHalfAdder

sampleRipple : (n : ℕ) → ℂ Bool ((↿ ⊠ n) ⊞ (↿ ⊠ n) ⊞ ↿) ((↿ ⊠ n) ⊞ ↿)
sampleRipple zero = {!!}
sampleRipple (suc m) = {!

      pid || ((pUncons || pUncons) ⟫ pIntertwine)
    ⟫                addBlock
    ⟫              pCons || pid

!}

    where
        addBlock : ∀ {α} → ℂ α (↿  ⊞  ( (↿ ⊞ ↿) ⊞ (↿ ⊠ m ⊞ ↿ ⊠ m) ))
                      ((↿ ⊞ ↿ ⊠ m) ⊞ ↿)
        addBlock = {!!}
