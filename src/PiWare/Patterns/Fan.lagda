\begin{code}
module PiWare.Patterns.Fan where

open import Function using (_∘_; _$_; id)
open import Data.Nat.Base using (suc; _+_)
open import Data.Vec using (Vec; _∷_; [_]; map; _++_)
open import Data.Vec.Extra using (initLast′)
open import Data.Product using (uncurry′) renaming (map to map×)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Vec.Extra using (VecNaturalT)
\end{code}


\begin{code}
fan-⊕-M : ∀ n → VecNaturalT (suc n) (n + 2)
fan-⊕-M n = record { op = fan-⊕-M-op; op-<$> = fan-⊕-M-<$> }
  where
    fan-⊕-M-op : ∀ {α : Set} → Vec α (suc n) → Vec α (n + 2)
    fan-⊕-M-op (x ∷ xs) = uncurry′ _++_ ∘ map× id (λ y → x ∷ [ y ]) ∘ initLast′ $ (x ∷ xs)

    postulate fan-⊕-M-<$> :   ∀ {α β} (f : α → β) (xs : Vec α (suc n))  -- parametricity
                              → fan-⊕-M-op (map f xs) ≡ map f (fan-⊕-M-op xs)
\end{code}
