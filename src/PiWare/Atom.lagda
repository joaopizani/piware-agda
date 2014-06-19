\begin{code}
module PiWare.Atom where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


%<*Atomic>
\begin{code}
record Atomic : Set₁ where
    field
        -- primitives
        Atom   : Set
        |Atom| : ℕ
        n→atom : Fin |Atom| → Atom
        atom→n : Atom → Fin |Atom|

        -- properties
        inv-left  : ∀ i → atom→n (n→atom i) ≡ i
        inv-right : ∀ a → n→atom (atom→n a) ≡ a

    Atom# : Set
    Atom# = Fin |Atom|
\end{code}
%</Atomic>
