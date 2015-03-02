\begin{code}
module Relation.Binary.Indexed.Core.Extra where

open import Level using (Level; suc; _⊔_)
open import Function using (flip)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Indexed.Core using (REL; Rel)
\end{code}


\begin{code}
_⇒_ : ∀ {i₁ i₂ a b ℓ₁ ℓ₂} {I₁ : Set i₁} {I₂ : Set i₂} {A : I₁ → Set a} {B : I₂ → Set b} → REL A B ℓ₁ → REL A B ℓ₂ → Set _
_⇒_ {A = A} {B = B} P Q = ∀ {i₁ i₂} {x : A i₁} {y : B i₂} → P x y → Q x y 

_⇒′_ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} {A : I → Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
_⇒′_ {A = A} P Q = ∀ {i₁ i₂} {x : A i₁} {y : A i₂} → P x y → Q x y

Pred : ∀ {a i} {I : Set i} → (I → Set a) → (ℓ : Level) → Set (i ⊔ a ⊔ suc ℓ)
Pred A ℓ = ∀ {i} → A i → Set ℓ

_Respects_ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} {A : I → Set a} → Pred A ℓ₁ → Rel A ℓ₂ → Set _
_Respects_ {A = A} P _∼_ = ∀ {i₁ i₂} {x : A i₁} {y : A i₂} → x ∼ y → P x → P y

_Respects₂_ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} {A : I → Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂)
_Respects₂_ {A = A} R _∼_ =
      (∀ {i} {x : A i} → _Respects_ {A = A} (R x)      _∼_)
    × (∀ {i} {y : A i} → _Respects_ {A = A} (flip R y) _∼_)


-- Indexed equality
infix 4 _≡_ _≢_

data _≡_ {i} {a} {I : Set i} {A : I → Set a} : ∀ {i₁ i₂} (x : A i₁) (y : A i₂) → Set (a ⊔ i) where
    refl : ∀ {i₁} (x : A i₁) → x ≡ x

_≢_ : ∀ {i} {a} {I : Set i} {A : I → Set a} {i₁ i₂} (x : A i₁) (y : A i₂) → Set _
_≢_ {A = A} x y = ¬ (_≡_ {A = A} x y)
\end{code}
