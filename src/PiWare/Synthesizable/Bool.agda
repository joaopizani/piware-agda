module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Vec using (Vec; [_]; head)

import PiWare.Synthesizable
open PiWare.Synthesizable 𝔹 public


-- basic instance
⇓𝕎⇑-𝔹 : ⇓𝕎⇑ 𝔹
⇓𝕎⇑-𝔹 = ⇓𝕎⇑[ [_] , head ]


-- TODO: should we also put "derivable" instances (found by recursive resolution) here?
⇓𝕎⇑-Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n)
⇓𝕎⇑-Vec𝔹 = ⇓𝕎⇑-Vec

⇓𝕎⇑-𝔹×𝔹 : ⇓𝕎⇑ (𝔹 × 𝔹)
⇓𝕎⇑-𝔹×𝔹 = ⇓𝕎⇑-×

⇓𝕎⇑-[𝔹×𝔹]×𝔹      : ⇓𝕎⇑ ((𝔹 × 𝔹) × 𝔹)
⇓𝕎⇑-𝔹×[𝔹×𝔹]      : ⇓𝕎⇑ (𝔹 × (𝔹 × 𝔹))
⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ (𝔹 × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] : ⇓𝕎⇑ (𝔹 × ((𝔹 × 𝔹) × 𝔹))
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] : ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × 𝔹))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × 𝔹)
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 : ⇓𝕎⇑ (((𝔹 × 𝔹) × 𝔹) × 𝔹)

⇓𝕎⇑-[𝔹×𝔹]×𝔹      = ⇓𝕎⇑-[a×b]×c
⇓𝕎⇑-𝔹×[𝔹×𝔹]      = ⇓𝕎⇑-a×[b×c]
⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-a×[b×[c×d]]
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] = ⇓𝕎⇑-a×[[b×c]×d]
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] = ⇓𝕎⇑-[a×b]×[c×d]
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 = ⇓𝕎⇑-[a×[b×c]]×d
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 = ⇓𝕎⇑-[[a×b]×c]×d
