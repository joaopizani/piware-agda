\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation {At : Atomic} (Gt : Gates At) where

open import Function using (_∘′_)
open import Data.Nat using (ℕ)
open import Data.Stream using (Stream; map)

open import PiWare.Circuit Gt using (ℂ̂; Mkℂ̂)
open import PiWare.Simulation.Core Gt using (⟦_⟧; ⟦_⟧*)
open import PiWare.Synthesizable At using (module ⇓W⇑)
open ⇓W⇑ ⦃ ... ⦄ using (⇓; ⇑)
\end{code}


%<*eval>
\AgdaTarget{⟦\_⟧̂}
\begin{code}
⟦_⟧̂ : ∀ {α i β j} → ℂ̂ α β {i} {j} → (α → β)
⟦ Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ c ⟧̂ = ⇑ ∘′ ⟦ c ⟧ ∘′ ⇓
\end{code}
%</eval>

%<*eval-seq>
\AgdaTarget{⟦\_⟧̂*}
\begin{code}
⟦_⟧̂* : ∀ {α i β j} → ℂ̂ α β {i} {j} → (Stream α → Stream β)
⟦ Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ c ⟧̂* = map ⇑ ∘′ ⟦ c ⟧* ∘′ map ⇓
\end{code}
%</eval-seq>
