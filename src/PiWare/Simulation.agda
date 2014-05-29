open import PiWare.Atom using (AtomInfo)

module PiWare.Simulation (AI : AtomInfo) where

open import Data.Nat using (ℕ)
open import Data.Bool using () renaming (Bool to 𝔹)

open import Data.Stream using (Stream) renaming (map to smap)

open import PiWare.Circuit AI 
open import PiWare.Synthesizable AI
open import PiWare.Simulation.Core


open ⇓𝕎⇑ {{...}}

⟦_⟧ : ∀ {α i β j} → ℂ α β {i} {j} → (α → β)
⟦_⟧ (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') a = ⇑ (⟦ c' ⟧' (⇓ a))

⟦_⟧* : ∀ {α i β j} → ℂ* α β {i} {j} → (Stream α → Stream β)
⟦_⟧* (Mkℂ* ⦃ sα ⦄ ⦃ sβ ⦄ c') a = smap ⇑ (⟦ c' ⟧*' (smap ⇓ a))
