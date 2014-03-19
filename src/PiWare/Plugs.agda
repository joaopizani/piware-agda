module PiWare.Plugs where

open import Function using (id)
open import Data.Sum using (inj₁; inj₂)
open import PiWare.Wires
open import PiWare.Circuit


-- identity
pid : ∀ {α w} → ℂ α w w
pid = Plug id

-- forking
fork2 : ∀ {α w} → ℂ α w (w ⊞ w)
fork2 = Plug fork2′
    where fork2′ : ∀ {w} → ⟬ w ⊞ w ⟭ → ⟬ w ⟭
          fork2′ (inj₁ x) = x
          fork2′ (inj₂ y) = y


-- associativity plugs
pALR : ∀ {α w v y} → ℂ α ((w ⊞ v) ⊞ y) (w ⊞ (v ⊞ y))
pALR = Plug pALR′
    where pALR′ : ∀ {w v y} → ⟬ w ⊞ (v ⊞ y) ⟭ → ⟬ (w ⊞ v) ⊞ y ⟭
          pALR′ (inj₁ l)         = inj₁ (inj₁ l)
          pALR′ (inj₂ (inj₁ rl)) = inj₁ (inj₂ rl)
          pALR′ (inj₂ (inj₂ rr)) = inj₂ rr

pARL : ∀ {α w v y} → ℂ α (w ⊞ (v ⊞ y)) ((w ⊞ v) ⊞ y)
pARL = Plug pARL′
    where pARL′ : ∀ {w v y} → ⟬ (w ⊞ v) ⊞ y ⟭ → ⟬ w ⊞ (v ⊞ y) ⟭
          pARL′ (inj₁ (inj₁ ll)) = inj₁ ll
          pARL′ (inj₁ (inj₂ lr)) = inj₂ (inj₁ lr)
          pARL′ (inj₂ r)         = inj₂ (inj₂ r)
