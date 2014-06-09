\begin{code}
module PiWare.Samples where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec)

import Algebra as Alg
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (Alg.CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)

open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Synthesizable.Bool
open import PiWare.Plugs Atom𝔹
open import PiWare.Circuit.Core
open import PiWare.Circuit Atom𝔹
\end{code}


\begin{code}
¬ℂ : ℂ 𝔹 𝔹
¬ℂ = Mkℂ Not
\end{code}

\begin{code}
∧ℂ : ℂ (𝔹 × 𝔹) 𝔹
∧ℂ = Mkℂ And 
\end{code}

\begin{code}
∨ℂ : ℂ (𝔹 × 𝔹) 𝔹
∨ℂ = Mkℂ Or
\end{code}


\begin{code}
¬×3ℂ : ℂ 𝔹 𝔹
¬×3ℂ = ¬ℂ ⟫ ¬ℂ ⟫ ¬ℂ
\end{code}

\begin{code}
¬∧ℂ : ℂ (𝔹 × 𝔹) 𝔹
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}

\begin{code}
⊻ℂ : ℂ (𝔹 × 𝔹) 𝔹
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ
\end{code}

\begin{code}
hadd : ℂ (𝔹 × 𝔹) (𝔹 × 𝔹)  -- a × b → c × s
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ
\end{code}

\begin{code}
fadd : ℂ ((𝔹 × 𝔹) × 𝔹) (𝔹 × 𝔹)  -- (a × b) × cin → co × s
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid
\end{code}


-- MUXES
\begin{code}
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×[𝔹×𝔹] ⇓𝕎⇑-𝔹×[𝔹×𝔹]
\end{code}

-- TODO: booleans for now. How to make it generic?
-- Look at lava: do we need an if-then-else constructor in the BASE CIRCUIT TYPE?
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
\begin{code}
mux2to1 : ℂ (𝔹 × (𝔹 × 𝔹)) 𝔹
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ
\end{code}


-- Sequential. In: (repeat false)   Out: cycle [false, true]...
\begin{code}
toggle : ℂ* 𝔹 𝔹
toggle = delayℂ (⊻ℂ ⟫ ¬ℂ ⟫ pFork×)
\end{code}


-- input × load → out
\begin{code}
reg : ℂ* (𝔹 × 𝔹) 𝔹
reg = delayℂ (pSwap || pid ⟫ pALR ⟫ (pid || pSwap) ⟫ mux2to1 ⟫ pFork×)
\end{code}


-- (attempt at) generically-sized mux
-- open module ℕ-CS = Alg.CommutativeSemiring ℕ-commSemiring using (+-identity)

-- private
--   ⇓𝕎⇑-𝔹×Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (𝔹 × Vec 𝔹 n)
--   ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n × Vec 𝔹 (2 ^ n))
--   ⇓𝕎⇑-[𝔹×Vec𝔹]×Vec𝔹2^n : {n : ℕ} → ⇓𝕎⇑ ((𝔹 × Vec 𝔹 n) × Vec 𝔹 (2 ^ n))
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 (2 ^ n)))
--   ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ ((Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] : {n : ℕ} → ⇓𝕎⇑ (𝔹 × (Vec 𝔹 n × Vec 𝔹 n) × (Vec 𝔹 (2 ^ n) × Vec 𝔹 (2 ^ n)))

--   ⇓𝕎⇑-𝔹×Vec𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n = ⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-[𝔹×Vec𝔹]×Vec𝔹2^n = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹×Vec𝔹 ⇓𝕎⇑-Vec𝔹
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹2^n] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-Vec𝔹×Vec𝔹2^n
--   ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] = ⇓𝕎⇑-× (⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹) (⇓𝕎⇑-× ⇓𝕎⇑-Vec𝔹 ⇓𝕎⇑-Vec𝔹)
--   ⇓𝕎⇑-𝔹×[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n] = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-[Vec𝔹×Vec𝔹]×[Vec𝔹2^n×Vec𝔹2^n]

-- mux : (n : ℕ) → let A = Vec 𝔹 n  in  ℂ (A × Vec 𝔹 (2 ^ n)) 𝔹 {2 ^ n} {1}
-- mux zero = pSnd ⟫ pSingletonOut
-- mux (suc n) rewrite (proj₂ +-identity) (2 ^ n) =
--       pUncons || pid
--     ⟫        pALR
--     ⟫ pid ||  pFork× || pVecHalfPow
--     ⟫ pid ||     pIntertwine
--     ⟫ pid ||   mux n || mux n
--     ⟫              mux2to1
