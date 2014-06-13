\begin{code}
module PiWare.Simulation where

open import Data.Nat using (ℕ)
open import Data.Stream using (Stream) renaming (map to smap)

-- TODO: now hardcoded to Atom𝔹, parameterize later
open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Circuit Atom𝔹
open import PiWare.Synthesizable Atom𝔹
open import PiWare.Simulation.Core

open ⇓𝕎⇑ {{...}}
\end{code}


%<*eval>
\begin{code}
⟦_⟧ : ∀ {α i β j} → (c : ℂ α β {i} {j}) {p : comb c} → (α → β)
⟦_⟧ (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') a = ⇑ (⟦ c' ⟧' (⇓ a))
\end{code}
%</eval>

%<*eval*>
\begin{code}
⟦_⟧* : ∀ {α i β j} → ℂ α β {i} {j} → (Stream α → Stream β)
⟦_⟧* (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') a = smap ⇑ (⟦ c' ⟧*' (smap ⇓ a))
\end{code}
%</eval*>
