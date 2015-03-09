\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_; const)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_×_; uncurry; _,_; proj₁)

open import PiWare.Circuit Gt using (ℂ; σ; _∥_)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Simulation Gt using (⟦_⟧)
open Atomic At using (W; Atom)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (from-≡; to-≡; _≈_; length-equal; []-cong; _∷-cong_) renaming (refl to reflᵥ; sym to symᵥ; trans to transᵥ)
open import Relation.Binary as B using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.Indexed.Core using (Setoid; IsEquivalence)

import Relation.Binary.Indexed.EqReasoning as IdxEqReasoning
\end{code}


\begin{code}
proj₁≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
proj₁≡ refl = refl

proj₂≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
proj₂≡ refl = refl

≡×≡⇒×≡× : ∀ {a b} {α : Set a} {β : Set b} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ ≡ a₂) × (b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
≡×≡⇒×≡× {a₁ = a₁} {a₂ = .a₁} {b₁ = b₁} {b₂ = .b₁} (refl , refl) = refl


ℂ₍₎ : (ℕ × ℕ) → Set
ℂ₍₎ = uncurry (ℂ {σ})




_≊_ : ∀ {i o i′ o′} → ℂ i o → ℂ i′ o′ → Set
_≊_ {i} {_} {i′} {_} c₁ c₂ = ∀ {w : W i} {w′ : W i′} → w ≈ w′ → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ w′

data _≋_ {i₁ o₁ i₂ o₂} : ℂ i₁ o₁ → ℂ i₂ o₂ → Set where
  refl≋ : {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} (i≡ : i₁ ≡ i₂) → c₁ ≊ c₂ → c₁ ≋ c₂

infixl 3 _≋_


≊⇒≋ : ∀ {i o₁ o₂} {c₁ : ℂ i o₁} {c₂ : ℂ i o₂} → (∀ w → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ w) → c₁ ≋ c₂
≊⇒≋ {i} {c₁ = c₁} {c₂} c₁≊c₂ = refl≋ refl ≈⇒≊
  where ≈⇒≊ : {w₁ w₂ : W i} → w₁ ≈ w₂ → ⟦ c₁ ⟧ w₁ ≈ ⟦ c₂ ⟧ w₂
        ≈⇒≊ w₁≈w₂ rewrite to-≡ w₁≈w₂ = c₁≊c₂ _


≋-refl : ∀ {i o} {c : ℂ i o} → c ≋ c
≋-refl = ≊⇒≋ (λ _ → reflᵥ _)

≋-sym : ∀ {i o i′ o′} {c₁ : ℂ i o} {c₂ : ℂ i′ o′} → c₁ ≋ c₂ → c₂ ≋ c₁
≋-sym (refl≋ refl c₁≊c₂) = ≊⇒≋ (symᵥ ∘ c₁≊c₂ ∘ symᵥ ∘ reflᵥ)

≋-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} {c₃ : ℂ i₃ o₃} → c₁ ≋ c₂ → c₂ ≋ c₃ → c₁ ≋ c₃
≋-trans (refl≋ refl c₁≊c₂) (refl≋ refl c₂≊c₃) = ≊⇒≋ (λ w → transᵥ (c₁≊c₂ $ reflᵥ w) (c₂≊c₃ $ reflᵥ w))

≋-isEquivalence : IsEquivalence ℂ₍₎ _≋_
≋-isEquivalence = record
  { refl  = ≋-refl
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }


≋-setoid : Setoid (ℕ × ℕ) _ _
≋-setoid = record
  { Carrier       = ℂ₍₎
  ; _≈_           = _≋_
  ; isEquivalence = ≋-isEquivalence
  }



open IdxEqReasoning ≋-setoid public
  using (begin_; _∎)
  renaming ( _≈⟨_⟩_ to _≈ℂ⟨_⟩_
           ; _≡⟨_⟩_ to _≡ℂ⟨_⟩_
           ; _≡⟨⟩_  to _≡ℂ⟨⟩_
           )


-- Testing the whole shebang
idℂ₂ : ℂ₍₎ (2 , 2)
idℂ₂ = id⤨ 

idℂ₂′ : ℂ₍₎ (1 + 1 , 1 + 1)
idℂ₂′ = id⤨ {1} ∥ id⤨ {1}

-- cheating a little, real proofs in another module
postulate id⤨-∥-idempotent : ∀ {n m} → id⤨ {n + m} ≋ id⤨ {n} ∥ id⤨ {m}

idℂ₂≋idℂ₂′ : idℂ₂ ≋ idℂ₂′
idℂ₂≋idℂ₂′ =
  begin
    idℂ₂
  ≈ℂ⟨ id⤨-∥-idempotent ⟩
    idℂ₂′
  ∎
\end{code}
