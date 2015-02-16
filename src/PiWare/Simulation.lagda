\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Stream using (Stream) renaming (map to mapₛ)

open import PiWare.Synthesizable At
open import PiWare.Circuit Gt using (ℂ; Mkℂ)
open import PiWare.Simulation.Core Gt using (⟦_⟧'; ⟦_⟧*')

open ⇓W⇑ ⦃ ... ⦄ using (⇓; ⇑)
\end{code}


%<*eval>
\begin{code}
⟦_⟧ : ∀ {α i β j} → ℂ α β {i} {j} → (α → β)
⟦ Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c' ⟧ = ⇑ ∘ ⟦ c' ⟧' ∘ ⇓
\end{code}
%</eval>

%<*eval-seq>
\begin{code}
⟦_⟧* : ∀ {α i β j} → ℂ α β {i} {j} → (Stream α → Stream β)
⟦ Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c' ⟧* = mapₛ ⇑ ∘ ⟦ c' ⟧*' ∘ mapₛ ⇓
\end{code}
%</eval-seq>
