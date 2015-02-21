\begin{code}
module Data.Vec.Extra where

open import Function using (id; _∘_)
open import Data.Nat using (zero; suc; _+_; _*_)
open import Data.Vec using (Vec; splitAt; []; _∷_; _++_; group)
open import Data.Product using (_×_; _,_; map; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


%<*splitAt-noproof>
\AgdaTarget{splitAt'}
\begin{code}
splitAt' : ∀ {ℓ} {α : Set ℓ} m {n} → Vec α (m + n) → Vec α m × Vec α n
splitAt' m v = map id proj₁ (splitAt m v)
\end{code}
%</splitAt-noproof>


%<*splitAt-proj₁>
\AgdaTarget{splitAt-proj₁}
\begin{code}
splitAt-proj₁ : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) → proj₁ (splitAt i₁ (v₁ ++ v₂)) ≡ v₁
splitAt-proj₁ {i₁ = zero}  []       _  = refl
splitAt-proj₁ {i₁ = suc n} (v ∷ vs) v₂ with splitAt n (vs ++ v₂) | splitAt-proj₁ vs v₂
splitAt-proj₁ {i₁ = suc n} (v ∷ vs) v₂ | _ , _ , eq              | ind rewrite eq | ind = refl
\end{code}
%</splitAt-proj₁>


%<*splitAt-proj₂>
\AgdaTarget{splitAt-proj₂}
\begin{code}
splitAt-proj₂ : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) → proj₁ (proj₂ (splitAt i₁ (v₁ ++ v₂))) ≡ v₂
splitAt-proj₂ {i₁ = zero}  []       _  = refl
splitAt-proj₂ {i₁ = suc n} (v ∷ vs) v₂ with splitAt n (vs ++ v₂) | splitAt-proj₂ vs v₂
splitAt-proj₂ {i₁ = suc n} (v ∷ vs) v₂ | _ , _ , eq              | ind rewrite eq | ind = refl
\end{code}
%</splitAt-proj₂>


%<*group-noproof>
\AgdaTarget{group'}
\begin{code}
group' : ∀ {ℓ} {α : Set ℓ} n k → Vec α (n * k) → Vec (Vec α k) n
group' n k = proj₁ ∘ group n k
\end{code}
%</group-noproof>
