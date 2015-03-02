\begin{code}
open import Relation.Binary.Indexed.Core using (Setoid; module Setoid)

module Relation.Binary.Indexed.EqReasoning {i} {I : Set i} {c} {ℓ} (S : Setoid I c ℓ) where

open import Relation.Binary.Indexed.Extra using (setoidPreorder)
\end{code}


\begin{code}
open import Relation.Binary.Indexed.PreorderReasoning (setoidPreorder S) public
  using (begin_; _∎)
  renaming ( _∼⟨_⟩_ to _≈⟨_⟩_
           ; _≈⟨_⟩_ to _≡⟨_⟩_
           ; _≈⟨⟩_  to _≡⟨⟩_
           )
\end{code}
