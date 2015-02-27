\begin{code}
module RelationBinaryIndexed where

open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Indexed.Core using (Rel; IsEquivalence; module IsEquivalence)
open import Relation.Binary.Indexed using (Transitive; Reflexive)
\end{code}


\begin{code}
record IsPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) (_≈_ : Rel A ℓ₁) (_∼_ : Rel A ℓ₂) : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
        isEquivalence : IsEquivalence A _≈_
        reflexive : _≈_ ⇒ _∼_
        trans : Transitive A _∼_

    module Eq = IsEquivalence isEquivalence

    refl : Reflexive A _∼_
    refl = reflexive Eq.refl


record Preorder {i} (I : Set i) c ℓ₁ ℓ₂ : Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _∼_
    field
        Carrier : I → Set c
        _≈_ : Rel Carrier ℓ₁
        _∼_ : Rel Carrier ℓ₂
        isPreorder : IsPreorder Carrier _≈_ _∼_

    open IsPreorder isPreorder public
\end{code}
