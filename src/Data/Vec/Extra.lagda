\begin{code}
module Data.Vec.Extra where

open import Function using (id; _∘_; _$_)
open import Data.Nat using (zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; map; proj₁; proj₂)
open import Data.Vec using (Vec; splitAt; []; _∷_; _++_; group)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Data.Vec.Properties using (module UsingVectorEquality)
open module VecPropertiesEq {a} {A : Set a} = UsingVectorEquality (setoid A) using (xs++[]=xs)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecEqPropositional)
open VecEqPropositional using (_≈_; sym; trans; []-cong; _∷-cong_; from-≡)
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


%<*splitAt-i+0>
\begin{code}
splitAt-i+0 : ∀ {ℓ} {α : Set ℓ} {i} {v : Vec α (i + 0)} {w : Vec α i} (v≈w : v ≈ w) → proj₁ (splitAt i v) ≈ w
splitAt-i+0 {i = i} {v} v≈w with splitAt i v
splitAt-i+0 v≈w | v′ , [] , refl = trans (sym $ xs++[]=xs v′) v≈w
\end{code}
%</splitAt-i+0>


%<*group-noproof>
\AgdaTarget{group'}
\begin{code}
group' : ∀ {ℓ} {α : Set ℓ} n k → Vec α (n * k) → Vec (Vec α k) n
group' n k = proj₁ ∘ group n k
\end{code}
%</group-noproof>


\begin{code}
≈-++-prefix : ∀ {n₁ n₂ ℓ} {α : Set ℓ} {v₁ w₁ : Vec α n₁} {v₂ w₂ : Vec α n₂} → v₁ ++ v₂ ≈ w₁ ++ w₂ → v₁ ≈ w₁
≈-++-prefix {v₁ = []}       {[]}       _                  = []-cong
≈-++-prefix {v₁ = x₁ ∷ xs₁} {y₁ ∷ ys₁} (x≡y ∷-cong xs≈ys) = x≡y ∷-cong (≈-++-prefix xs≈ys)

≈-++-suffix : ∀ {n₁ n₂ ℓ} {α : Set ℓ} {v₁ w₁ : Vec α n₁} {v₂ w₂ : Vec α n₂} → v₁ ++ v₂ ≈ w₁ ++ w₂ → v₂ ≈ w₂
≈-++-suffix {v₁ = []}       {[]}       v₂≈w₂              = v₂≈w₂
≈-++-suffix {v₁ = x₁ ∷ xs₁} {y₁ ∷ ys₁} (x≡y ∷-cong xs≈ys) = ≈-++-suffix {v₁ = xs₁} {ys₁} xs≈ys

++-assoc : ∀ {n₁ n₂ n₃ ℓ} {α : Set ℓ} (v₁ : Vec α n₁) (v₂ : Vec α n₂) (v₃ : Vec α n₃) → (v₁ ++ v₂) ++ v₃ ≈ v₁ ++ (v₂ ++ v₃)
++-assoc []         _ _ = from-≡ refl
++-assoc (x₁ ∷ xs₁) _ _ = refl ∷-cong (++-assoc xs₁ _ _)

++-assoc-split₁ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                  → v₁ ≈ v₂ → proj₁ (splitAt n (proj₁ (splitAt (n + m) v₁))) ≈ proj₁ (splitAt n v₂)
++-assoc-split₁ = {!!}
\end{code}
