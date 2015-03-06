\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_)
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
coerce : ∀ {ℓ n m} {α : Set ℓ} {p : n ≡ m} → Vec α n → Vec α m
coerce {p = eq} rewrite eq = id

proj₁≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
proj₁≡ refl = refl

proj₂≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
proj₂≡ refl = refl

≡×≡⇒×≡× : ∀ {a b} {α : Set a} {β : Set b} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ ≡ a₂) × (b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
≡×≡⇒×≡× {a₁ = a₁} {a₂ = .a₁} {b₁ = b₁} {b₂ = .b₁} (refl , refl) = refl


ℂ₍₎ : (ℕ × ℕ) → Set
ℂ₍₎ = uncurry (ℂ {σ})


_≅_ : ∀ {io} → ℂ₍₎ io → ℂ₍₎ io → Set
_≅_ {i , _} c₁ c₂ = ∀ (w : W i) → ⟦ c₁ ⟧ w ≡ ⟦ c₂ ⟧ w

data _≣_ {io : ℕ × ℕ} : ℂ₍₎ io → ℂ₍₎ io → Set where
  refl≣ : {c₁ c₂ : ℂ₍₎ io} → c₁ ≅ c₂ → c₁ ≣ c₂

infixl 3 _≣_

≣-refl : ∀ {io} {c : ℂ₍₎ io} → c ≣ c
≣-refl {_} {c} = refl≣ (λ w → refl)

≣-sym : ∀ {io} {c₁ c₂ : ℂ₍₎ io} → c₁ ≣ c₂ → c₂ ≣ c₁
≣-sym (refl≣ eq) = refl≣ (sym ∘ eq)

≣-trans : ∀ {io} {c₁ c₂ c₃ : ℂ₍₎ io} → c₁ ≣ c₂ → c₂ ≣ c₃ → c₁ ≣ c₃
≣-trans (refl≣ eq₁₂) (refl≣ eq₂₃) = refl≣ $ λ w → trans (eq₁₂ w) (eq₂₃ w)

≣-isEquivalence : ∀ {io} → B.IsEquivalence (_≣_ {io})
≣-isEquivalence = record
  { refl  = ≣-refl
  ; sym   = ≣-sym
  ; trans = ≣-trans
  }



_≊_ : ∀ {io io′} → ℂ₍₎ io → ℂ₍₎ io′ → Set
_≊_ {i , _} {i′ , _} c₁ c₂ = ∀ {w : W i} {w′ : W i′} → w ≈ w′ → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ w′

data _≋_ {io₁ io₂} : ℂ₍₎ io₁ → ℂ₍₎ io₂ → Set where
  refl≋ : {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} → c₁ ≊ c₂ → c₁ ≋ c₂

infixl 3 _≋_

≋-refl : ∀ {io} {c : ℂ₍₎ io} → c ≋ c
≋-refl {_} {c} = refl≋ (from-≡ ∘ cong ⟦ c ⟧ ∘ to-≡) -- (reflᵥ ∘ ⟦ c ⟧)
 
≋-sym : ∀ {io io′} {c₁ : ℂ₍₎ io} {c₂ : ℂ₍₎ io′} → c₁ ≋ c₂ → c₂ ≋ c₁
≋-sym (refl≋ c₁≊c₂) = refl≋ (symᵥ ∘ c₁≊c₂ ∘ symᵥ)
 
≋-trans : ∀ {io₁ io₂ io₃} {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} {c₃ : ℂ₍₎ io₃} → c₁ ≋ c₂ → c₂ ≋ c₃ → c₁ ≋ c₃
≋-trans (refl≋ c₁≊c₂) (refl≋ c₂≊c₃) = refl≋ (λ {w} {w′} p → transᵥ (c₁≊c₂ {w} {{!w!}} {!!}) (c₂≊c₃ {!!}))

≊-trans : ∀ {io₁ io₂ io₃} {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} {c₃ : ℂ₍₎ io₃} → c₁ ≊ c₂ → c₂ ≊ c₃ → c₁ ≊ c₃
≊-trans eq₁ eq₂ = {!!}

≋-isEquivalence : IsEquivalence ℂ₍₎ _≋_
≋-isEquivalence = record
  { refl  = ≋-refl
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }


≣-setoid : ∀ {io} → B.Setoid _ _
≣-setoid {io} = record
  { Carrier       = ℂ₍₎ io
  ; _≈_           = _≣_
  ; isEquivalence = ≣-isEquivalence
  } 

≋-setoid : Setoid (ℕ × ℕ) _ _
≋-setoid = record
  { Carrier       = ℂ₍₎
  ; _≈_           = _≋_
  ; isEquivalence = ≋-isEquivalence
  }



≣⇒≋ : ∀ {i o} {c₁ c₂ : ℂ i o} → c₁ ≣ c₂ → c₁ ≋ c₂
≣⇒≋ (refl≣ eq) = refl≋ {!!} 


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
