\begin{code}
module PiWare.Atom where

open import Level using (_⊔_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; module ≡-Reasoning)
open import Function.Inverse using (_↔_)
\end{code}


\begin{code}
Injective′ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → (α → β) → Set _
Injective′ f = ∀ {x y} → f x ≡ f y → x ≡ y


record Injection′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to        : α → β
    injective : Injective′ to


record Equivalence′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to   : α → β
    from : β → α


_LeftInverseOf′_ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → (β → α) → (α → β) → Set _
f LeftInverseOf′ g = ∀ x → f (g x) ≡ x

_RightInverseOf′_ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → (β → α) → (α → β) → Set _
f RightInverseOf′ g = g LeftInverseOf′ f


record Surjective′ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} (to : α → β) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    from             : β → α
    right-inverse-of : from RightInverseOf′ to


record LeftInverse′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to              : α → β
    from            : β → α
    left-inverse-of : from LeftInverseOf′ to

  open ≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)

  injective : Injective′ to
  injective {x} {y} eq = begin
    x           ≡⟨ sym (left-inverse-of x) ⟩
    from (to x) ≡⟨ cong from eq ⟩
    from (to y) ≡⟨ left-inverse-of y ⟩
    y           ∎

  injection : Injection′ α β
  injection = record { to = to;  injective = injective }

  equivalence : Equivalence′ α β
  equivalence = record { to = to;  from = from }

  to-from : ∀ {x y} → to x ≡ y → from y ≡ x
  to-from {x} {y} to-x≡y = begin
    from y      ≡⟨ cong from (sym to-x≡y) ⟩
    from (to x) ≡⟨ left-inverse-of x ⟩
    x           ∎


RightInverse′ : ∀ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) → Set _
RightInverse′ α β = LeftInverse′ β α


record Surjection′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to         : α → β
    surjective : Surjective′ to

  open Surjective′ surjective public

  right-inverse : RightInverse′ α β
  right-inverse = record { to              = from
                         ; from            = to
                         ; left-inverse-of = right-inverse-of
                         }

  open LeftInverse′ right-inverse public using () renaming (to-from to from-to)

  injective : Injective′ from
  injective = LeftInverse′.injective right-inverse

  injection : Injection′ β α
  injection = LeftInverse′.injection right-inverse

  equivalence : Equivalence′ α β
  equivalence = record { to   = to
                       ; from = from
                       }


record Bijective′ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} (to : α → β) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    injective  : Injective′  to
    surjective : Surjective′ to

  open Surjective′ surjective public

  left-inverse-of : from LeftInverseOf′ to
  left-inverse-of x = injective (right-inverse-of (to x))


record Bijection′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to : α → β
    bijective : Bijective′ to

  open Bijective′ bijective public

  injection : Injection′ α β
  injection = record { to = to;  injective = injective }

  surjection : Surjection′ α β
  surjection = record { to = to;  surjective = surjective }

  open Surjection′ surjection public using (equivalence; right-inverse; from-to)

  left-inverse : LeftInverse′ α β
  left-inverse = record { to = to
                        ; from = from
                        ; left-inverse-of = left-inverse-of
                        }

  open LeftInverse′ left-inverse public using (to-from)


record _InverseOf′_ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} (from : β → α) (to : α → β) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    left-inverse-of  : from LeftInverseOf′  to
    right-inverse-of : from RightInverseOf′ to


record Inverse′ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to : α → β
    from : β → α
    inverse-of : from InverseOf′ to

  open _InverseOf′_ inverse-of public

  left-inverse : LeftInverse′ α β
  left-inverse = record { to              = to
                        ; from            = from
                        ; left-inverse-of = left-inverse-of
                        }

  open LeftInverse′ left-inverse public using (injective; injection)

  bijection : Bijection′ α β
  bijection = record { to        = to
                     ; bijective = record { injective  = injective
                                          ; surjective = record { from             = from
                                                                ; right-inverse-of = right-inverse-of
                                                                }
                                          }
                     }

  open Bijection′ bijection public using (equivalence; surjective; surjection; right-inverse; to-from; from-to)


_↔′_ : ∀ {ℓ₁ ℓ₂} (α : Set ℓ₁) (β : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
α ↔′ β = Inverse′ α β
\end{code}


%<*Atomic>
\AgdaTarget{Atomic, Atom, |Atom|-1, enum, |Atom|, Atom\#, W}
\begin{code}
record Atomic : Set₁ where
    field
        Atom     : Set
        |Atom|-1 : ℕ

        enum     : Fin (suc |Atom|-1) ↔′ Atom

    |Atom| = suc |Atom|-1
    Atom#  = Fin |Atom|
    W = Vec Atom
\end{code}
%</Atomic>
