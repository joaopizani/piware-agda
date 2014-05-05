module PiWare.Simulation where

open import Data.Nat using (ℕ)

open import PiWare.Circuit
open import PiWare.Synthesizable.Bool
open import PiWare.Simulation.Core


open ⇓𝕎⇑ {{...}}

⟦_⟧ : {α β : Set} {#α #β : ℕ} → ℂ α β {#α} {#β} → (α → β)
⟦_⟧ {#α = k} (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ cc) a = ⇑ (core⟦ cc ⟧ (⇓ a))
