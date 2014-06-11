\begin{code}
module PiWare.Atom where

open import Data.Nat using (ℕ; _≤_)
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


%<*AtomInfo>
\begin{code}
record AtomInfo : Set₁ where
    field
        -- primitives
        Atom   : Set
        card   : ℕ
        n→atom : Fin card → Atom
        atom→n : Atom → Fin card

        -- properties
        inv-left  : ∀ i → atom→n (n→atom i) ≡ i
        inv-right : ∀ a → n→atom (atom→n a) ≡ a

    Atom# : Set
    Atom# = Fin card
\end{code}
%</AtomInfo>
