module PiWare.Plugs where

open import Function using (id)
open import Data.Sum using (inj₁; inj₂)
open import PiWare.Wires
open import PiWare.Circuit


pid : ∀ {α w} → ℂ α w w
pid = Plug id

fork2 : ∀ {α w} → ℂ α w (w ⊞ w)
fork2 = Plug fork2′
    where fork2′ : ∀ {w} → ⟬ w ⊞ w ⟭ → ⟬ w ⟭
          fork2′ (inj₁ x) = x
          fork2′ (inj₂ y) = y
