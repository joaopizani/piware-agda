\begin{code}
open import RelationBinaryIndexed using (Preorder; module Preorder)

module RelationBinaryIndexedPreorderReasoning
    {i} {I : Set i} {c} {ℓ₁} {ℓ₂} (P : Preorder I c ℓ₁ ℓ₂) where

open import Level using (suc)
\end{code}

\begin{code}
open Preorder P using (_∼_; _≈_; refl; trans; reflexive) renaming (Carrier to A)

infix 4 _RelTo_
infix 3 _∎
infix 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
infix 1 begin_

data _RelTo_ {i₁ i₂} (x : A i₁) (y : A i₂) : Set (suc ℓ₂) where
    relTo : (x∼y : x ∼ y) → x RelTo y

begin_ : ∀ {i₁ i₂} {x : A i₁} {y : A i₂} → x RelTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ {i₁ i₂ i₃} (x : A i₁) {y : A i₂} {z : A i₃} → x ∼ y → y RelTo z → x RelTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z) 

_≈⟨_⟩_ : ∀ {i₁ i₂ i₃} (x : A i₁) {y : A i₂} {z : A i₃} → x ≈ y → y RelTo z → x RelTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)

_≈⟨⟩_ : ∀ {i₁ i₂} (x : A i₁) {y : A i₂} → x RelTo y → x RelTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : ∀ {i₁} (x : A i₁) → x RelTo x
_∎ _ = relTo refl
\end{code}
