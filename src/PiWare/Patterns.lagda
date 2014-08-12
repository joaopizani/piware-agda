\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _*_)
open import Data.Vec using (Vec)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-Vec)
open import PiWare.Circuit Gt using (ℂ; Mkℂ)
open import PiWare.Patterns.Core Gt using (pars'; seqs')
\end{code}


%<*pars>
\begin{code}
pars : ∀ {k α i β j} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ α β {i} {j} → ℂ (Vec α k) (Vec β k) {k * i} {k * j}
pars {k = k} {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') = Mkℂ ⦃ ⇓W⇑-Vec ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec ⦃ sβ ⦄ ⦄ (pars' {k} {i} {j} c')
\end{code}
%</pars>


%<*seqs>
\begin{code}
seqs : (k : ℕ) → ∀ {α i} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ α α {i} {i} → ℂ α α {i} {i}
seqs k ⦃ sα ⦄ (Mkℂ c') = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ (seqs' k c')
\end{code}
%</seqs>
