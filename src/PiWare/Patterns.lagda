\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _*_)
open import Data.Vec using (Vec)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-Vec)
open import PiWare.Circuit Gt using (ℂ; Mkℂ)
open import PiWare.Patterns.Core Gt using (parsN'; seqsN')
\end{code}


%<*parsN>
\begin{code}
parsN : ∀ {k α i β j p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄
        → ℂ {p} α β {i} {j} → ℂ {p} (Vec α k) (Vec β k) {k * i} {k * j}
parsN {k = k} {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ c') =
    Mkℂ ⦃ ⇓W⇑-Vec ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec ⦃ sβ ⦄ ⦄ (parsN' {k} {i} {j} c')
\end{code}
%</parsN>


%<*seqsN>
\begin{code}
seqsN : ∀ (k : ℕ) {α i p} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂ {p} α α {i} {i} → ℂ {p} α α {i} {i}
seqsN k ⦃ sα ⦄ (Mkℂ c') = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ (seqsN' k c')
\end{code}
%</seqsN>
