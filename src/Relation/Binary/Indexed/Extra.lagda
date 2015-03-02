\begin{code}
module Relation.Binary.Indexed.Extra where

open import Level using (suc; _⊔_)
open import Function using (_$_)
open import Data.Product using (_,_)
open import Relation.Binary.Indexed using (Transitive; Reflexive)
open import Relation.Binary.Indexed.Core using (Rel; IsEquivalence; module IsEquivalence; Setoid; module Setoid)

open import Relation.Binary.Indexed.Core.Extra using (_⇒′_; _Respects₂_; _≡_)
\end{code}


\begin{code}
record IsPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                  (_≈_ : Rel A ℓ₁)  -- The underlying equality
                  (_∼_ : Rel A ℓ₂)  -- The relation "under consideration"
                  : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence A _≈_
    reflexive     : _⇒′_ {A = A} _≈_ _∼_  -- Expressed in terms of the underlying equality
    trans         : Transitive A _∼_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive A _∼_
  refl = reflexive Eq.refl
  
  ∼-resp-≈ : _Respects₂_ {A = A} _∼_ _≈_
  ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive x≈y))
           , (λ x≈y x∼z → trans (reflexive $ Eq.sym x≈y) x∼z)


record Preorder {i} (I : Set i) c ℓ₁ ℓ₂ : Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : I → Set c
    _≈_        : Rel Carrier ℓ₁
    _∼_        : Rel Carrier ℓ₂
    isPreorder : IsPreorder Carrier _≈_ _∼_

  open IsPreorder isPreorder public


setoidIsPreorder : ∀ {i c ℓ} {I : Set i} (S : Setoid I c ℓ)
                   → let open Setoid S  in  IsPreorder Carrier (_≡_ {A = Carrier}) _≈_
setoidIsPreorder S =
  let open Setoid S
  in record
       { isEquivalence = {!!}
       ; reflexive     = {!reflexive!}
       ; trans         = {!!}
       }
\end{code}
