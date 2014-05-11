module PiWare.Simulation where

open import Data.Nat using (ℕ)
open import Data.Bool using () renaming (Bool to 𝔹)

open import PiWare.Circuit
open import PiWare.Synthesizable.Bool
open import PiWare.Simulation.Core


open ⇓𝕎⇑ {{...}}

⟦_⟧ : {α β : Set} {#α #β : ℕ} → ℂ 𝔹 α β {#α} {#β} → (α → β)
⟦_⟧ (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ cc) a = ⇑ (⟦ cc ⟧' (⇓ a))
