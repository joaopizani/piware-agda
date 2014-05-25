module PiWare.Padding where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product using (∃; _,_)
open import Data.Vec using (Vec; _++_; replicate; take)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


-- Maximum view: gives a proof for the maximum of two naturals, along with their ordering
data _⊔''_ : ℕ → ℕ → Set where
    fst : {a b : ℕ} → a ⊔ b ≡ a → b ≤ a → a ⊔'' b
    snd : {a b : ℕ} → a ⊔ b ≡ b → a ≤ b → a ⊔'' b

-- View function for the maximum view
_⊔'_ : (a b : ℕ) → a ⊔'' b
zero     ⊔' zero    = fst refl z≤n
zero     ⊔' (suc _) = snd refl z≤n
(suc _)  ⊔' zero    = fst refl z≤n
(suc a') ⊔' (suc b') with a' ⊔' b'
(suc a') ⊔' (suc b') | fst m le = fst (cong suc m) (s≤s le)
(suc a') ⊔' (suc b') | snd m le = snd (cong suc m) (s≤s le)

-- Given an less-than-or-equal proof between two naturals, give the equality proof for the difference (δ)
getδ : ∀ {x y} → x ≤ y → ∃ (λ δ → y ≡ x + δ)
getδ z≤n = _ , refl
getδ (s≤s le) with getδ le
... | δ , eq = δ , cong suc eq


padFst : {α : Set} (x y : ℕ) → α → Vec α x → Vec α (x ⊔ y)
padFst x y e v with x ⊔' y
... | fst m le rewrite m = v
... | snd m le rewrite m with getδ le
...                           | δ , eq rewrite eq = v ++ replicate e

padSnd : {α : Set} (x y : ℕ) → α → Vec α y → Vec α (x ⊔ y)
padSnd x y e v with x ⊔' y
... | snd m le rewrite m = v
... | fst m le rewrite m with getδ le
...                      | δ , eq rewrite eq = v ++ replicate e


unpadFst : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α x
unpadFst x y v with x ⊔' y
unpadFst x y v | fst m le rewrite m = v
unpadFst x y v | snd m le rewrite m with getδ le
...                                 | _ , eq rewrite eq = take x v

unpadSnd : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α y
unpadSnd x y v with x ⊔' y
unpadSnd x y v | snd m le rewrite m = v
unpadSnd x y v | fst m le rewrite m with getδ le
...                                      | _ , eq rewrite eq = take y v
