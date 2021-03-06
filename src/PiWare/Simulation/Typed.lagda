\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Typed {At : Atomic} (Gt : Gates At) where

open import Function using (_∘′_)
open import Data.Stream using (Stream; map)

open import PiWare.Circuit.Typed Gt using (ℂ̂; Mkℂ̂)
open import PiWare.Simulation Gt using (⟦_⟧; ⟦_⟧ω)
open import PiWare.Synthesizable At using (module ⇓W⇑)
\end{code}

\begin{code}
open ⇓W⇑ ⦃ ... ⦄ using (⇓; ⇑)
\end{code}


%<*eval-typed>
\AgdaTarget{⟦\_⟧̂}
\begin{code}
⟦_⟧̂ : ∀ {α i β j} → ℂ̂ α β {i} {j} → (α → β)
⟦ Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ c ⟧̂ = ⇑ ∘′ ⟦ c ⟧ ∘′ ⇓
\end{code}
%</eval-typed>

%<*eval-seq-typed>
\AgdaTarget{⟦\_⟧̂*}
\begin{code}
⟦_⟧̂ω : ∀ {α i β j} → ℂ̂ α β {i} {j} → (Stream α → Stream β)
⟦ Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ c ⟧̂ω = map ⇑ ∘′ ⟦ c ⟧ω ∘′ map ⇓
\end{code}
%</eval-seq-typed>
