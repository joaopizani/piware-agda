\begin{code}
module Relation.Binary.Indexed.Equality.Core where

open import Relation.Binary.Indexed.Core using (Symmetric; Transitive; IsEquivalence)

open import Relation.Binary.Indexed.Core.Extra using (_≡_; refl)
\end{code}


\begin{code}
sym : ∀ {i a} {I : Set i} {A : I → Set a} → Symmetric A (_≡_ {A = A})
sym refl = refl

trans : ∀ {i a} {I : Set i} {A : I → Set a} → Transitive A (_≡_ {A = A})
trans refl eq = eq

isEquivalence : ∀ {i a} {I : Set i} {A : I → Set a} → IsEquivalence A (_≡_ {A = A})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
\end{code}
