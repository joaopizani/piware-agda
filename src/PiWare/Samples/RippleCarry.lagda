\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to 𝔹)

open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Circuit Atom𝔹
open import PiWare.Plugs Atom𝔹
open import PiWare.Synthesizable.Bool

open import PiWare.Samples using (fadd)
\end{code}


\begin{code}
private
\end{code}
  %<*sample-ripple-Synth-types>
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
  %</sample-ripple-Synth-types>

  %<*sample-ripple-Synth-defs>
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
  %</sample-ripple-Synth-defs>


-- cin × a × b → s × cout
%<*sample-ripple>
\begin{code}
ripple : (n : ℕ) →  let W = Vec 𝔹 n  in  ℂ (𝔹 × W × W) (W × 𝔹)
ripple zero    = pid || pFst ⟫ pSwap
ripple (suc m) =   pid || (pUncons || pUncons ⟫ pIntertwine)
                 ⟫ middle
                 ⟫ pCons || pid
  where pAssoc = pARL ⟫ pARL || pid
        middle = pAssoc ⟫ (fadd || pid) ⟫ pALR ⟫ (pid || ripple m) ⟫ pARL
\end{code}
%</sample-ripple>
