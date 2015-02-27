\begin{code}
module RelationBinaryIndexedCore where

open import Relation.Binary.Indexed.Core using (REL)
\end{code}


\begin{code}
_⇒_ : ∀ {i₁ i₂ a b ℓ₁ ℓ₂} {I₁ : Set i₁} {I₂ : Set i₂} {A : I₁ → Set a} {B : I₂ → Set b} → REL A B ℓ₁ → REL A B ℓ₂ → Set _
_⇒_ {A = A} {B = B} P Q = ∀ {i₁ i₂} {x : A i₁} {y : B i₂} → P x y → Q x y 
\end{code}
