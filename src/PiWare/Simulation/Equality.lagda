\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (_$_; id; _∘_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; uncurry; _,_; proj₁)
open import Level using () renaming (zero to lzero)

open import PiWare.Circuit Gt using (ℂ; σ)
open import PiWare.Simulation Gt using (⟦_⟧)
open Atomic At using (W; Atom)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (_≈_) renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary.Indexed
    using (Rel; Reflexive; IsEquivalence) renaming (Setoid to ISetoid)

\end{code}


\begin{code}
ℂ₍₎ : (ℕ × ℕ) → Set
ℂ₍₎ = uncurry (ℂ {σ})

coerce : ∀ {ℓ n m} {α : Set ℓ} {p : n ≡ m} → Vec α n → Vec α m
coerce {p = eq} rewrite eq = id

proj₁≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
proj₁≡ refl = refl

proj₂≡ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} {a₁ a₂ : α} {b₁ b₂ : β} → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
proj₂≡ refl = refl

module ≋ where

  ≊ : ∀ {io₁ io₂} (p : io₁ ≡ io₂) → ℂ₍₎ io₁ → ℂ₍₎ io₂ → Set
  ≊ {i₁ , o₁} {i₂ , o₂} p c₁ c₂ = ∀ (w : W i₁) → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ (coerce {p = proj₁≡ p} w)

  data _≋_ {io₁ io₂ : ℕ × ℕ} : ℂ₍₎ io₁ → ℂ₍₎ io₂ → Set where
      refl≋ : (p : io₁ ≡ io₂) {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} → ≊ p c₁ c₂ → c₁ ≋ c₂

  infixl 4 _≋_

open ≋ using (_≋_; refl≋) public

≋-refl : ∀ {io} {c : ℂ₍₎ io} → c ≋ c
≋-refl {_} {c} = refl≋ refl (≈-refl ∘ ⟦ c ⟧)
 
≋-sym : ∀ {io₁ io₂} {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} → c₁ ≋ c₂ → c₂ ≋ c₁
≋-sym (refl≋ refl c₁≊c₂) = refl≋ refl (≈-sym ∘ c₁≊c₂)
 
≋-trans : ∀ {io₁ io₂ io₃} {c₁ : ℂ₍₎ io₁} {c₂ : ℂ₍₎ io₂} {c₃ : ℂ₍₎ io₃} → c₁ ≋ c₂ → c₂ ≋ c₃ → c₁ ≋ c₃
≋-trans (refl≋ refl c₁≊c₂) (refl≋ refl c₂≊c₃) = refl≋ refl (λ w → ≈-trans (c₁≊c₂ w) (c₂≊c₃ w))
 
setoid : ISetoid (ℕ × ℕ) _ _
setoid =
    record {
        Carrier = ℂ₍₎
      ; _≈_     = _≋_
      ; isEquivalence = record {
            refl  = ≋-refl
          ; sym   = ≋-sym
          ; trans = ≋-trans
        }
    }
\end{code}

