\begin{code}
module PiWare.Padding where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product using (∃; _,_)
open import Data.Vec using (Vec; _++_; replicate; take)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}


-- Maximum view: gives a proof for the maximum of two naturals, along with their ordering
\begin{code}
data _⊔''_ : ℕ → ℕ → Set where
    max₁ : {a b : ℕ} → a ⊔ b ≡ a → b ≤ a → a ⊔'' b
    max₂ : {a b : ℕ} → a ⊔ b ≡ b → a ≤ b → a ⊔'' b
\end{code}

-- View function for the maximum view
\begin{code}
_⊔'_ : (a b : ℕ) → a ⊔'' b
zero     ⊔' zero    = max₁ refl z≤n
zero     ⊔' (suc _) = max₂ refl z≤n
(suc _)  ⊔' zero    = max₁ refl z≤n
(suc a') ⊔' (suc b') with a' ⊔' b'
(suc a') ⊔' (suc b') | max₁ m le = max₁ (cong suc m) (s≤s le)
(suc a') ⊔' (suc b') | max₂ m le = max₂ (cong suc m) (s≤s le)
\end{code}

-- Given an less-than-or-equal proof between two naturals, give the equality proof for the difference (δ)
\begin{code}
getδ : ∀ {x y} → x ≤ y → ∃ (λ δ → y ≡ x + δ)
getδ z≤n = _ , refl
getδ (s≤s le) with getδ le
... | δ , eq = δ , cong suc eq
\end{code}


\begin{code}
padFst : {α : Set} (x y : ℕ) → α → Vec α x → Vec α (x ⊔ y)
padFst x y e v with x ⊔' y
... | max₁ m le rewrite m = v
... | max₂ m le rewrite m with getδ le
...                       | δ , eq rewrite eq = v ++ replicate e
\end{code}

\begin{code}
padSnd : {α : Set} (x y : ℕ) → α → Vec α y → Vec α (x ⊔ y)
padSnd x y e v with x ⊔' y
... | max₂ m le rewrite m = v
... | max₁ m le rewrite m with getδ le
...                       | δ , eq rewrite eq = v ++ replicate e
\end{code}


\begin{code}
unpadFst : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α x
unpadFst x y v with x ⊔' y
unpadFst x y v | max₁ m le rewrite m = v
unpadFst x y v | max₂ m le rewrite m with getδ le
...                                  | _ , eq rewrite eq = take x v
\end{code}

\begin{code}
unpadSnd : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α y
unpadSnd x y v with x ⊔' y
unpadSnd x y v | max₂ m le rewrite m = v
unpadSnd x y v | max₁ m le rewrite m with getδ le
...                                  | _ , eq rewrite eq = take y v
\end{code}
