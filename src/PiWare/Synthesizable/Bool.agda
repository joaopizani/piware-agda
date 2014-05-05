module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Vec using (Vec; [_]) renaming ([] to ε; _∷_ to _◁_)

import PiWare.Synthesizable
open PiWare.Synthesizable 𝔹 public


-- basic instance
⇓𝕎⇑-𝔹 : ⇓𝕎⇑ 𝔹
⇓𝕎⇑-𝔹 = ⇓𝕎⇑[ down , up ]
    where down : 𝔹 → 𝕎 _
          down b = [ b ]
          
          up : 𝕎 _ → 𝔹
          up (bit ◁ ε) = bit


-- TODO: should we also put "derivable" instances (if we had recursive resolution) here?
⇓𝕎⇑-Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n)
⇓𝕎⇑-Vec𝔹 = ⇓𝕎⇑-Vec

⇓𝕎⇑-𝔹×𝔹 : ⇓𝕎⇑ (𝔹 × 𝔹)
⇓𝕎⇑-𝔹×𝔹 = ⇓𝕎⇑-×

⇓𝕎⇑-[𝔹×𝔹]×𝔹 : ⇓𝕎⇑ ((𝔹 × 𝔹) × 𝔹)
⇓𝕎⇑-[𝔹×𝔹]×𝔹 = ⇓𝕎⇑-×

⇓𝕎⇑-𝔹×[𝔹×𝔹] : ⇓𝕎⇑ (𝔹 × (𝔹 × 𝔹))
⇓𝕎⇑-𝔹×[𝔹×𝔹] = ⇓𝕎⇑-×
