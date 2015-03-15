\begin{code}
open import Relation.Binary.Indexed.Extra using (Preorder; module Preorder)

module Relation.Binary.Indexed.PreorderReasoning
    {i} {I : Set i} {c} {ℓ₁} {ℓ₂} (P : Preorder I c ℓ₁ ℓ₂) where

open import Level using (suc)
open Preorder P using (_∼_; _≈_; refl; trans; reflexive) renaming (Carrier to A)
\end{code}

\begin{code}
infix 4 _IsRelatedTo_
infix 3 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
infix 1 begin_

data _IsRelatedTo_ {i₁ i₂} (x : A i₁) (y : A i₂) : Set (suc ℓ₂) where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {i₁ i₂} {x : A i₁} {y : A i₂} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ {i₁ i₂ i₃} (x : A i₁) {y : A i₂} {z : A i₃} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z) 

_≈⟨_⟩_ : ∀ {i₁ i₂ i₃} (x : A i₁) {y : A i₂} {z : A i₃} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)

_≈⟨⟩_ : ∀ {i₁ i₂} (x : A i₁) {y : A i₂} → x IsRelatedTo y → x IsRelatedTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : ∀ {i₁} (x : A i₁) → x IsRelatedTo x
_∎ _ = relTo refl
\end{code}
