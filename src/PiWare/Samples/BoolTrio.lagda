\begin{code}
module PiWare.Samples.BoolTrio where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec)
open import Data.Unit using (⊤)

import Algebra as A
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (A.CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool

open import PiWare.Gates.BoolTrio using (BoolTrio; FalseConst#; TrueConst#; Not#; And#; Or#)
open import PiWare.Plugs BoolTrio
open import PiWare.Circuit.Core BoolTrio
open import PiWare.Circuit BoolTrio
\end{code}


%<*fundamentals>
\begin{code}
⊥ℂ ⊤ℂ : ℂ ⊤ B
⊥ℂ = Mkℂ (Gate FalseConst#)
⊤ℂ = Mkℂ (Gate TrueConst#)

¬ℂ : ℂ B B
¬ℂ = Mkℂ (Gate Not#)

∧ℂ ∨ℂ : ℂ (B × B) B
∧ℂ = Mkℂ (Gate And#) 
∨ℂ = Mkℂ (Gate Or#)
\end{code}
%</fundamentals>

%<*nand>
\begin{code}
¬∧ℂ : ℂ (B × B) B
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}
%</nand>

%<*xor>
\begin{code}
⊻ℂ : ℂ (B × B) B
⊻ℂ =   pFork×
     ⟫ (¬ℂ || pid ⟫ ∧ℂ) || (pid || ¬ℂ ⟫ ∧ℂ)
     ⟫ ∨ℂ
\end{code}
%</xor>

%<*hadd>
\begin{code}
hadd : ℂ (B × B) (B × B)  -- a × b → c × s
hadd =   pFork×
       ⟫ ∧ℂ || ⊻ℂ
\end{code}
%</hadd>

%<*fadd>
\begin{code}
fadd : ℂ ((B × B) × B) (B × B)  -- (a × b) × cin → co × s
fadd =   hadd || pid
       ⟫    pALR
       ⟫ pid  || hadd
       ⟫    pARL
       ⟫ ∨ℂ   || pid
\end{code}
%</fadd>


%<*mux2to1-Synth>
\begin{code}
⇓W⇑-[B×[B×B]]×[B×[B×B]] : ⇓W⇑ ((B × (B × B)) × (B × (B × B)))
⇓W⇑-[B×[B×B]]×[B×[B×B]] = ⇓W⇑-× ⇓W⇑-B×[B×B] ⇓W⇑-B×[B×B]
\end{code}
%</mux2to1-Synth>

-- TODO: booleans for now. How to make it generic?  Maybe using the sum constructor.
-- (s × (a × b)) → z:   z = (a ∧ ¬ s) ∨ (b ∧ s)
%<*mux2to1>
\begin{code}
mux2to1 : ℂ (B × (B × B)) B
mux2to1 =   pFork×
          ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
          ⟫ ∨ℂ
\end{code}
%</mux2to1>


-- Sequential.  Out: cycle [true, false]...
%<*shift>
\begin{code}
shift : ℂ B B
shift = delayℂ pSwap
\end{code}
%</shift>

%<*toggle>
\begin{code}
toggle : ℂ ⊤ B
toggle = ⊥ℂ ⟫ delayℂ (∨ℂ ⟫ ¬ℂ ⟫ pFork×)
\end{code}
%</toggle>


-- input × load → out
%<*reg>
\begin{code}
reg : ℂ (B × B) B
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
--   ⇓W⇑-B×VecB : ∀ {n} → ⇓W⇑ (B × Vec B n)
--   ⇓W⇑-VecB×VecB2^n : ∀ {n} → ⇓W⇑ (Vec B n × Vec B (2 ^ n))
--   ⇓W⇑-[B×VecB]×VecB2^n : {n : ℕ} → ⇓W⇑ ((B × Vec B n) × Vec B (2 ^ n))
--   ⇓W⇑-B×[VecB×VecB2^n] : {n : ℕ} → ⇓W⇑ (B × (Vec B n × Vec B (2 ^ n)))
--   ⇓W⇑-[VecB×VecB]×[VecB2^n×VecB2^n] : {n : ℕ} → ⇓W⇑ ((Vec B n × Vec B n) × (Vec B (2 ^ n) × Vec B (2 ^ n)))
--   ⇓W⇑-B×[VecB×VecB]×[VecB2^n×VecB2^n] : {n : ℕ} → ⇓W⇑ (B × (Vec B n × Vec B n) × (Vec B (2 ^ n) × Vec B (2 ^ n)))
--   \end{code}
--   %</sample-mux-Synth-types>

--   %<*sample-mux-Synth-defs>
--   \begin{code}
--   ⇓W⇑-B×VecB = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-VecB
--   ⇓W⇑-VecB×VecB2^n = ⇓W⇑-× ⇓W⇑-VecB ⇓W⇑-VecB
--   ⇓W⇑-[B×VecB]×VecB2^n = ⇓W⇑-× ⇓W⇑-B×VecB ⇓W⇑-VecB
--   ⇓W⇑-B×[VecB×VecB2^n] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-VecB×VecB2^n
--   ⇓W⇑-[VecB×VecB]×[VecB2^n×VecB2^n] = ⇓W⇑-× (⇓W⇑-× ⇓W⇑-VecB ⇓W⇑-VecB) (⇓W⇑-× ⇓W⇑-VecB ⇓W⇑-VecB)
--   ⇓W⇑-B×[VecB×VecB]×[VecB2^n×VecB2^n] = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-[VecB×VecB]×[VecB2^n×VecB2^n]
--   \end{code}
--   %</sample-mux-Synth-defs>

-- %<*sample-mux>
-- \begin{code}
-- mux : (n : ℕ) → let A = Vec B n  in  ℂ (A × Vec B (2 ^ n)) B {2 ^ n} {1}
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
