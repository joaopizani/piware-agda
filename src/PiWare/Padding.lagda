\begin{code}
module PiWare.Padding where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product using (_,_; Σ; Σ-syntax)
open import Data.Vec using (Vec; _++_; replicate; take)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}


-- Maximum view: gives a proof for the maximum of two naturals, along with their ordering
%<*MaxView>
\begin{code}
data _⊔''_ : ℕ → ℕ → Set where
    max₁ : {a b : ℕ} → a ⊔ b ≡ a → b ≤ a → a ⊔'' b
    max₂ : {a b : ℕ} → a ⊔ b ≡ b → a ≤ b → a ⊔'' b
\end{code}
%</MaxView>

-- View function for the maximum view
%<*maxView>
\begin{code}
_⊔'_ : (a b : ℕ) → a ⊔'' b
zero     ⊔' zero    = max₁ refl z≤n
(suc _)  ⊔' zero    = max₁ refl z≤n
zero     ⊔' (suc _) = max₂ refl z≤n
(suc a') ⊔' (suc b') with a' ⊔' b'
(suc a') ⊔' (suc b') | max₁ a⊔b≡a b≤a = max₁ (cong suc a⊔b≡a) (s≤s b≤a)
(suc a') ⊔' (suc b') | max₂ a⊔b≡b a≤b = max₂ (cong suc a⊔b≡b) (s≤s a≤b)
\end{code}
%</maxView>

-- Given a ≤ relation between two naturals, return the (proven) difference (δ)
%<*getDelta>
\begin{code}
getδ : ∀ {x y} → x ≤ y → Σ[ δ ∈ ℕ ] y ≡ x + δ
getδ z≤n = _ , refl
getδ (s≤s z≤w) with getδ z≤w
getδ (s≤s z≤w) | δ , w≡z+δ = δ , cong suc w≡z+δ
\end{code}
%</getDelta>


%<*padFst>
\begin{code}
padFst : {α : Set} (x y : ℕ) → α → Vec α x → Vec α (x ⊔ y)
padFst x y e v with x ⊔' y
... | max₁ x⊔y≡x y≤x rewrite x⊔y≡x = v
... | max₂ x⊔y≡y x≤y rewrite x⊔y≡y with getδ x≤y
...     | δ , y≡x+δ rewrite y≡x+δ = v ++ replicate e
\end{code}
%</padFst>

%<*padSnd>
\begin{code}
padSnd : {α : Set} (x y : ℕ) → α → Vec α y → Vec α (x ⊔ y)
padSnd x y e v with x ⊔' y
... | max₂ x⊔y≡y x≤y rewrite x⊔y≡y = v
... | max₁ x⊔y≡x y≤x rewrite x⊔y≡x with getδ y≤x
...     | δ , x≡y+δ rewrite x≡y+δ = v ++ replicate e
\end{code}
%</padSnd>

%<*unpadFst>
\begin{code}
unpadFst : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α x
unpadFst x y v with x ⊔' y
unpadFst x y v | max₁ x⊔y≡x y≤x rewrite x⊔y≡x = v
unpadFst x y v | max₂ x⊔y≡y x≤y rewrite x⊔y≡y with getδ x≤y
...                | _ , y≡x+δ rewrite y≡x+δ = take x v
\end{code}
%</unpadFst>

%<*unpadSnd>
\begin{code}
unpadSnd : {α : Set} (x y : ℕ) → Vec α (x ⊔ y) → Vec α y
unpadSnd x y v with x ⊔' y
unpadSnd x y v | max₂ x⊔y≡y x≤y rewrite x⊔y≡y = v
unpadSnd x y v | max₁ x⊔y≡x y≤x rewrite x⊔y≡x with getδ y≤x
...                | _ , x≡y+δ rewrite x≡y+δ = take y v
\end{code}
%</unpadSnd>
