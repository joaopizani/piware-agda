\begin{code}
module PiWare.Samples.BoolTrio where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (#_)
open import Data.Vec using (Vec)

import Algebra as A
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (A.CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)

open import PiWare.Atom.Bool using (Atomic-𝔹)
open import PiWare.Synthesizable Atomic-𝔹
open import PiWare.Synthesizable.Bool

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Plugs BoolTrio
open import PiWare.Circuit.Core BoolTrio
open import PiWare.Circuit BoolTrio
\end{code}


%<*fundamentals>
\begin{code}
¬ℂ : ℂ 𝔹 𝔹
¬ℂ = Mkℂ (Gate (# 0))

∧ℂ ∨ℂ : ℂ (𝔹 × 𝔹) 𝔹
∧ℂ = Mkℂ (Gate (# 1)) 
∨ℂ = Mkℂ (Gate (# 2))
\end{code}
%</fundamentals>


%<*not3x>
\begin{code}
¬×3ℂ : ℂ 𝔹 𝔹
¬×3ℂ = ¬ℂ ⟫ ¬ℂ ⟫ ¬ℂ
\end{code}
%</not3x>

%<*nand>
\begin{code}
¬∧ℂ : ℂ (𝔹 × 𝔹) 𝔹
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}
%</nand>

%<*xor>
\begin{code}
⊻ℂ : ℂ (𝔹 × 𝔹) 𝔹
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ
\end{code}
%</xor>

%<*hadd>
\begin{code}
hadd : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)  -- a × b → c × s
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ
\end{code}
%</hadd>

%<*fadd>
\begin{code}
fadd : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)  -- (a × b) × cin → co × s
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid
\end{code}
%</fadd>


%<*mux2to1-Synth>
\begin{code}
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×[𝔹×𝔹] ⇓𝕎⇑-𝔹×[𝔹×𝔹]
\end{code}
%</mux2to1-Synth>

-- TODO: booleans for now. How to make it generic?  Maybe using the sum constructor.
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
%<*mux2to1>
\begin{code}
mux2to1 : ℂ (𝔹 × (𝔹 × 𝔹)) 𝔹
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ
\end{code}
%</mux2to1>


-- Sequential. In: (repeat false)   Out: cycle [true, false]...
%<*toggle>
\begin{code}
toggle : ℂ 𝔹 𝔹
toggle = delayℂ (⊻ℂ ⟫ ¬ℂ ⟫ pFork×)
\end{code}
%</toggle>


-- input × load → out
%<*reg>
\begin{code}
reg : ℂ (𝔹 × 𝔹) 𝔹
reg = delayℂ (pSwap || pid ⟫ pALR ⟫ (pid || pSwap) ⟫ mux2to1 ⟫ pFork×)
\end{code}
%</reg>


-- (attempt at) generically-sized mux
-- \begin{code}
-- open module ℕ-CS = Alg.CommutativeSemiring ℕ-commSemiring using (+-identity)
-- \end{code}

-- \begin{code}
-- private
-- \end{code}
--   %<*sample-mux-Synth-types>
--   \begin{code}
--   ⇓𝕎⇑-𝔹×Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
--   ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n × Vec 𝔹 (2 ^ n))
--   ⇓𝕎⇑-[𝔹×Vec𝔹]×Vec𝔹2^n : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × Vec 𝔹 (2 ^ n))
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 (2 ^ n)))
--   ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ ((Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))
--   \end{code}
--   %</sample-mux-Synth-types>

--   %<*sample-mux-Synth-defs>
--   \begin{code}
--   ⇓𝕎⇑-𝔹×Vec𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n = ⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-[𝔹×Vec𝔹]×Vec𝔹2^n = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×Vec𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹2^n] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n
--   ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] = ⇓𝕎⇑-× (⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹) (⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹)
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n]
--   \end{code}
--   %</sample-mux-Synth-defs>

-- %<*sample-mux>
-- \begin{code}
-- mux : (n : ℕ) → let A = Vec 𝔹 n  in  ℂ (A × Vec 𝔹 (2 ^ n)) 𝔹 {2 ^ n} {1}
-- mux zero = pSnd ⟫ pSingletonOut
-- mux (suc n) rewrite (proj₂ +-identity) (2 ^ n) =
--       pUncons || pid
--     ⟫        pALR
--     ⟫ pid ||  pFork× || pVecHalfPow
--     ⟫ pid ||     pIntertwine
--     ⟫ pid ||   mux n || mux n
--     ⟫              mux2to1
-- \end{code}
-- %</sample-mux>
