\begin{code}
module Data.FiniteType.Base where

open import Function using (_⟨_⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Nat using (eq?)
open import Data.Fin using (Fin)

open import Function.Injection using (_↣_) renaming (_∘_ to _∘′_)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans; →-to-⟶)

open import Data.Fin.Properties.Extra using (toℕ↣)
\end{code}


%<*Finite>
\AgdaTarget{Finite, to∘from}
\begin{code}
record Finite {ℓ} (α : Set ℓ) : Set ℓ where
  field |α| : ℕ

  α# = Fin |α|

  field
    to      : α# → α
    from    : α → α#
    to∘from : ∀ x → to (from x) ≡ x
\end{code}
%</Finite>

%<*from-inj-eqn>
\AgdaTarget{from↣, \_≟ⁿ\_}
\begin{code}
  from↣ : α ↣ Fin |α|
  from↣ = record { to = →-to-⟶ from;  injective = from-inj }
    where from-inj : ∀ {x y} → from x ≡ from y → x ≡ y
          from-inj {x} {y} fromX≡fromY = sym (to∘from x) ⟨ trans ⟩ cong to fromX≡fromY ⟨ trans ⟩ to∘from y

  _≟ⁿ_ : Decidable {A = α} _≡_
  _≟ⁿ_ = eq? (toℕ↣ ∘′ from↣)
\end{code}
%</from-inj-eqn>

\begin{code}
  infix 4 _≟ⁿ_
\end{code}
