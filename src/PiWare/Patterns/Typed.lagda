\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns.Typed {At : Atomic} (Gt : Gates At) where

open import Data.Nat.Base using (ℕ; _*_)
open import Data.Vec using (Vec)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-Vec)
open import PiWare.Circuit.Typed Gt using (ℂ̂; Mkℂ̂)
open import PiWare.Patterns Gt using (parsN; seqsN)
\end{code}


--TODO: parŝ
--TODO: seqŝ


%<*parsN-typed>
\AgdaTarget{parsN̂}
\begin{code}
parsN̂ : ∀ {k α i β j p} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂ̂ {p} α β {i} {j} → ℂ̂ {p} (Vec α k) (Vec β k) {k * i} {k * j}
parsN̂ {k = k} {i = i} {j = j} {p = p} ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ̂ c) =
    Mkℂ̂ ⦃ ⇓W⇑-Vec ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec ⦃ sβ ⦄ ⦄ (parsN {k} {i} {j} {p} c)
\end{code}
%</parsN-typed>


%<*seqsN-typed>
\AgdaTarget{seqsN̂}
\begin{code}
seqsN̂ : ∀ k {α j p} ⦃ _ : ⇓W⇑ α {j} ⦄ → ℂ̂ {p} α α {j} {j} → ℂ̂ {p} α α {j} {j}
seqsN̂ k {p = p} ⦃ sα ⦄ (Mkℂ̂ c) = Mkℂ̂ ⦃ sα ⦄ ⦃ sα ⦄ (seqsN k {p = p} c)
\end{code}
%</seqsN-typed>
