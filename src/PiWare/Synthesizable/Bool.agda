module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Nat using (ℕ)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Vec using (Vec; head) renaming ([_] to singleton)

open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Synthesizable Atom𝔹 public


-- basic instance
⇓𝕎⇑-𝔹 : ⇓𝕎⇑ 𝔹
⇓𝕎⇑-𝔹 = ⇓𝕎⇑[ singleton , head ]


-- derivable instances (can be resolved recursively from the basics)
⇓𝕎⇑-𝔹×α : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (𝔹 × α)
⇓𝕎⇑-α×𝔹 : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (α × 𝔹)

⇓𝕎⇑-𝔹×α sα = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 sα
⇓𝕎⇑-α×𝔹 sα = ⇓𝕎⇑-× sα     ⇓𝕎⇑-𝔹


⇓𝕎⇑-Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n)
⇓𝕎⇑-Vec𝔹 = ⇓𝕎⇑-Vec ⇓𝕎⇑-𝔹


⇓𝕎⇑-𝔹⊎α : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (𝔹 ⊎ α)
⇓𝕎⇑-α⊎𝔹 : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (α ⊎ 𝔹)

⇓𝕎⇑-𝔹⊎α sα = ⇓𝕎⇑-⊎ ⇓𝕎⇑-𝔹 sα
⇓𝕎⇑-α⊎𝔹 sα = ⇓𝕎⇑-⊎ sα     ⇓𝕎⇑-𝔹


⇓𝕎⇑-[𝔹×𝔹]×𝔹 : ⇓𝕎⇑ ((𝔹 × 𝔹) × 𝔹)
⇓𝕎⇑-𝔹×[𝔹×𝔹] : ⇓𝕎⇑ (𝔹 × (𝔹 × 𝔹))

⇓𝕎⇑-[𝔹×𝔹]×𝔹 = ⇓𝕎⇑-[a×b]×c ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-𝔹×[𝔹×𝔹] = ⇓𝕎⇑-a×[b×c] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹

⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ (𝔹 × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] : ⇓𝕎⇑ (𝔹 × ((𝔹 × 𝔹) × 𝔹))
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] : ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × 𝔹))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × 𝔹)
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 : ⇓𝕎⇑ (((𝔹 × 𝔹) × 𝔹) × 𝔹)

⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-a×[b×[c×d]] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] = ⇓𝕎⇑-a×[[b×c]×d] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] = ⇓𝕎⇑-[a×b]×[c×d] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 = ⇓𝕎⇑-[a×[b×c]]×d ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 = ⇓𝕎⇑-[[a×b]×c]×d ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
