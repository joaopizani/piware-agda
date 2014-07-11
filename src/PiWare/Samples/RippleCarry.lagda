\begin{code}
module PiWare.Samples.RippleCarry where

open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using () renaming (Bool to B)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
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
  ⇓W⇑-B×VecB : {n : ℕ} → ⇓W⇑ (B × Vec B n)
  ⇓W⇑-VecB×B : {n : ℕ} → ⇓W⇑ (Vec B n × B)
  ⇓W⇑-VecB×VecB : {n : ℕ} → ⇓W⇑ (Vec B n × Vec B n)
  ⇓W⇑-B×[VecB×B] : {n : ℕ} → ⇓W⇑ (B × (Vec B n × B))
  ⇓W⇑-[B×VecB]×B : {n : ℕ} → ⇓W⇑ ((B × Vec B n) × B)
  ⇓W⇑-B×[VecB×VecB] : {n : ℕ} → ⇓W⇑ (B × (Vec B n × Vec B n))
  ⇓W⇑-B×[B×[VecB×VecB]] : {n : ℕ} → ⇓W⇑ (B × (B × (Vec B n × Vec B n)))
  ⇓W⇑-[B×VecB]×[B×VecB] : {n : ℕ} → ⇓W⇑ ((B × Vec B n) × (B × Vec B n))
  ⇓W⇑-[B×B]×[VecB×VecB] : {n : ℕ} → ⇓W⇑ ((B × B) × (Vec B n × Vec B n))
  ⇓W⇑-[B×B]×[B×VecB×VecB] : {n : ℕ} → ⇓W⇑ ((B × B) × (B × Vec B n × Vec B n))
  ⇓W⇑-B×[[B×B]×[VecB×VecB]] : {n : ℕ} → ⇓W⇑ (B × ((B × B) × (Vec B n × Vec B n)))
  ⇓W⇑-[B×[B×B]]×[VecB×VecB] : {n : ℕ} → ⇓W⇑ ((B × (B × B)) × (Vec B n × Vec B n))
  ⇓W⇑-[[B×B]×B]×[VecB×VecB] : {n : ℕ} → ⇓W⇑ (((B × B) × B) × (Vec B n × Vec B n))
  \end{code}
  %</Synth-types>

  %<*Synth-defs>
  \begin{code}
  ⇓W⇑-B×VecB = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-VecB
  ⇓W⇑-VecB×B = ⇓W⇑-× ⇓W⇑-VecB ⇓W⇑-B
  ⇓W⇑-B×[VecB×B] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-VecB×B
  ⇓W⇑-[B×VecB]×B = ⇓W⇑-× ⇓W⇑-B×VecB ⇓W⇑-B
  ⇓W⇑-VecB×VecB = ⇓W⇑-× ⇓W⇑-VecB ⇓W⇑-VecB
  ⇓W⇑-B×[VecB×VecB] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-VecB×VecB
  ⇓W⇑-B×[B×[VecB×VecB]] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-B×[VecB×VecB] 
  ⇓W⇑-[B×VecB]×[B×VecB] = ⇓W⇑-× ⇓W⇑-B×VecB ⇓W⇑-B×VecB
  ⇓W⇑-[B×B]×[VecB×VecB] = ⇓W⇑-× ⇓W⇑-B×B ⇓W⇑-VecB×VecB
  ⇓W⇑-[B×B]×[B×VecB×VecB] = ⇓W⇑-× ⇓W⇑-B×B ⇓W⇑-B×[VecB×VecB]
  ⇓W⇑-B×[[B×B]×[VecB×VecB]] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-[B×B]×[VecB×VecB]
  ⇓W⇑-[B×[B×B]]×[VecB×VecB] = ⇓W⇑-× ⇓W⇑-B×[B×B] ⇓W⇑-VecB×VecB
  ⇓W⇑-[[B×B]×B]×[VecB×VecB] = ⇓W⇑-× ⇓W⇑-[B×B]×B ⇓W⇑-VecB×VecB 
  \end{code}
  %</Synth-defs>


-- cin × a × b → s × cout
%<*ripple>
\begin{code}
ripple : (n : ℕ) →  let W = Vec B n  in  ℂ (B × W × W) (W × B)
ripple zero    = pid || pFst ⟫ pSwap
ripple (suc m) =
      pid   || (pUncons || pUncons ⟫ pIntertwine)
    ⟫     pAssoc
    ⟫ fadd  || pid
    ⟫      pALR
    ⟫ pid   || ripple m
    ⟫      pARL
    ⟫ pCons || pid
    where pAssoc = pARL ⟫ pARL || pid
\end{code}
%</ripple>
