module PiWare.Simulation where

open import Data.Nat using (ℕ)
open import Data.Bool using () renaming (Bool to 𝔹)

open import Data.Stream using (Stream) renaming (map to smap)

open import PiWare.Circuit 𝔹  -- TODO: will be parameterized with Atom
open import PiWare.Synthesizable.Bool
open import PiWare.Simulation.Core


open ⇓𝕎⇑ {{...}}

⟦_⟧ : {α β : Set} {#α #β : ℕ} → ℂ α β {#α} {#β} → (α → β)
⟦_⟧ (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') a = ⇑ (⟦ c' ⟧' (⇓ a))

⟦_⟧* : {α β : Set} {#α #β : ℕ} → ℂ* α β {#α} {#β} → (Stream α → Stream β)
⟦_⟧* (Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ c') a = smap ⇑ (⟦ c' ⟧*' (smap ⇓ a))
