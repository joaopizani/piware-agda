\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to 𝔹)

open import PiWare.Atom.Bool using (Atomic-𝔹)
open import PiWare.Synthesizable Atomic-𝔹
open import PiWare.Synthesizable.Bool

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit BoolTrio
open import PiWare.Plugs BoolTrio

open import PiWare.Samples.BoolTrio using (fadd)
\end{code}


\begin{code}
private
\end{code}
  %<*Synth-types>
  \begin{code}
  ⇓𝕎⇑-𝔹×Vec𝔹 : {n : ℕ} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
  ⇓𝕎⇑-Vec𝔹×𝔹 : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × 𝔹)
  ⇓𝕎⇑-Vec𝔹×Vec𝔹 : {n : ℕ} → ⇓𝕎⇑ (Vec 𝔹 n × Vec 𝔹 n)
  ⇓𝕎⇑-𝔹×[Vec𝔹×𝔹] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × 𝔹))
  ⇓𝕎⇑-[𝔹×Vec𝔹]×𝔹 : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × 𝔹)
  ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-𝔹×[𝔹×[Vec𝔹×Vec𝔹]] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (𝔹 × (Vec 𝔹 n × Vec 𝔹 n)))
  ⇓𝕎⇑-[𝔹×Vec𝔹]×[𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × (𝔹 × Vec 𝔹 n))
  ⇓𝕎⇑-[𝔹×𝔹]×[Vec𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-[𝔹×𝔹]×[𝔹×Vec𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-𝔹×[[𝔹×𝔹]×[Vec𝔹×Vec𝔹]] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × ((𝔹 × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n)))
  ⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[Vec𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (Vec 𝔹 n × Vec 𝔹 n))
  ⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×[Vec𝔹×Vec𝔹] : {n : ℕ} → ⇓𝕎⇑ (((𝔹 × 𝔹) × 𝔹) × (Vec 𝔹 n × Vec 𝔹 n))
  \end{code}
  %</Synth-types>

  %<*Synth-defs>
  \begin{code}
  ⇓𝕎⇑-𝔹×Vec𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹
  ⇓𝕎⇑-Vec𝔹×𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-𝔹
  ⇓𝕎⇑-𝔹×[Vec𝔹×𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹×𝔹
  ⇓𝕎⇑-[𝔹×Vec𝔹]×𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×Vec𝔹 ⇓𝕎⇑-𝔹
  ⇓𝕎⇑-Vec𝔹×Vec𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹
  ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹×Vec𝔹
  ⇓𝕎⇑-𝔹×[𝔹×[Vec𝔹×Vec𝔹]] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹] 
  ⇓𝕎⇑-[𝔹×Vec𝔹]×[𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×Vec𝔹 ⇓𝕎⇑-𝔹×Vec𝔹
  ⇓𝕎⇑-[𝔹×𝔹]×[Vec𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×𝔹 ⇓𝕎⇑-Vec𝔹×Vec𝔹
  ⇓𝕎⇑-[𝔹×𝔹]×[𝔹×Vec𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×𝔹 ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹]
  ⇓𝕎⇑-𝔹×[[𝔹×𝔹]×[Vec𝔹×Vec𝔹]] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-[𝔹×𝔹]×[Vec𝔹×Vec𝔹]
  ⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[Vec𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×[𝔹×𝔹] ⇓𝕎⇑-Vec𝔹×Vec𝔹
  ⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×[Vec𝔹×Vec𝔹] = ⇓𝕎⇑-× ⇓𝕎⇑-[𝔹×𝔹]×𝔹 ⇓𝕎⇑-Vec𝔹×Vec𝔹 
  \end{code}
  %</Synth-defs>


-- cin × a × b → s × cout
%<*ripple>
\begin{code}
ripple : (n : ℕ) →  let W = Vec 𝔹 n  in  ℂ (𝔹 × W × W) (W × 𝔹)
ripple zero    = pid || pFst ⟫ pSwap
ripple (suc m) =   pid || (pUncons || pUncons ⟫ pIntertwine)
                 ⟫ middle
                 ⟫ pCons || pid
  where pAssoc = pARL ⟫ pARL || pid
        middle = pAssoc ⟫ (fadd || pid) ⟫ pALR ⟫ (pid || ripple m) ⟫ pARL
\end{code}
%</ripple>
