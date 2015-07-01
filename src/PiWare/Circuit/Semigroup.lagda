\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Circuit.Semigroup {At : Atomic} {Gt : Gates At} where

open import PiWare.Circuit {Gt = Gt} using (𝐂; _⟫_; _∥_)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Simulation.Equality Gt using (_≋_)
\end{code}


\begin{code}
⊕𝐂-Ty : Set
⊕𝐂-Ty = 𝐂 2 1


⊕𝐂-IsAssoc : ⊕𝐂-Ty → Set
⊕𝐂-IsAssoc ⊕𝐂 = ⊕𝐂 ∥ id⤨₁ ⟫ ⊕𝐂 ≋ id⤨₁ ∥ ⊕𝐂 ⟫ ⊕𝐂
  where id⤨₁ = id⤨ {1}


record ⊕𝐂-Semigroup : Set where
  field
    ⊕𝐂 : ⊕𝐂-Ty
    isAssoc : ⊕𝐂-IsAssoc ⊕𝐂
\end{code}
