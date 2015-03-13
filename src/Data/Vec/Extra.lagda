\begin{code}
module Data.Vec.Extra where

open import Function using (id; _∘_; _∘′_; _$_)
open import Data.Nat using (zero; suc; _+_; _*_)
open import Data.Product using (∃₂; _×_; _,_; map; proj₁; proj₂)
open import Data.Vec using (Vec; splitAt; []; _∷_; _++_; group)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Data.Vec.Properties using (module UsingVectorEquality)
open module VecPropertiesEq {a} {A : Set a} = UsingVectorEquality (setoid A) using (xs++[]=xs)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecEqPropositional)
open VecEqPropositional using (_≈_; []-cong; _∷-cong_; from-≡; to-≡) renaming (sym to symᵥ; trans to transᵥ)
\end{code}


\begin{code}
proj₂′ : ∀ {n m ℓ} {α : Set ℓ} {xs : Vec α (n + m)} (_ : ∃₂ λ (ys : Vec α n) (zs : Vec α m) → xs ≡ ys ++ zs) → Vec α m
proj₂′ = proj₁ ∘ proj₂

₂′ : ∀ {n m ℓ} {α : Set ℓ} {xs : Vec α (n + m)} (_ : ∃₂ λ (ys : Vec α n) (zs : Vec α m) → xs ≡ ys ++ zs) → Vec α m
₂′ = proj₁ ∘ proj₂

₁ = proj₁
₂ = proj₂
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
splitAt-proj₂′ : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) → proj₂′ (splitAt i₁ (v₁ ++ v₂)) ≡ v₂
splitAt-proj₂′ {i₁ = zero}  []       _  = refl
splitAt-proj₂′ {i₁ = suc n} (v ∷ vs) v₂ with splitAt n (vs ++ v₂) | splitAt-proj₂′ vs v₂
splitAt-proj₂′ {i₁ = suc n} (v ∷ vs) v₂ | _ , _ , eq              | ind rewrite eq | ind = refl
\end{code}
%</splitAt-proj₂>


%<*splitAt-i+0>
\begin{code}
splitAt-i+0 : ∀ {ℓ} {α : Set ℓ} {i} {v : Vec α (i + 0)} {w : Vec α i} (v≈w : v ≈ w) → proj₁ (splitAt i v) ≈ w
splitAt-i+0 {i = i} {v} v≈w with splitAt i v
splitAt-i+0 v≈w | v′ , [] , refl = transᵥ (symᵥ $ xs++[]=xs v′) v≈w
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

module _ where
 pattern _,′_ left right = left , right , refl

 private
  ╍ = splitAt

 ++-assoc-split₁ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → (₁ ∘ ╍ n ∘ ₁) (╍ (n + m) v₁) ≈ ₁ (╍ n v₂)
 ++-assoc-split₁ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | (╍ n ∘ ₁) (╍ (n + m) xs) | ╍ n ys
 ++-assoc-split₁                        xs≈ys    | ._ ,′ xsₒ    | xsₙ ,′ xsₘ                | _ ,′ _ =
     ≈-++-prefix $ transᵥ (symᵥ $ ++-assoc xsₙ xsₘ xsₒ) xs≈ys
 
 
 ++-assoc-split₂ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → (₂′ ∘ ╍ n ∘ ₁) (╍ (n + m) v₁) ≈ (₁ ∘ ╍ m ∘ ₂′) (╍ n v₂)
 ++-assoc-split₂ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | (╍ n ∘ ₁) (╍ (n + m) xs) | ╍ n ys    | (╍ m ∘ ₂′) (╍ n ys)
 ++-assoc-split₂                        xs≈ys    | ._ ,′ _      | xsₙ ,′ _                 | ysₙ ,′ ._ | ysₘ ,′ ysₒ =
     ≈-++-suffix {v₁ = xsₙ} {ysₙ} $ ≈-++-prefix $ transᵥ xs≈ys (symᵥ $ ++-assoc ysₙ ysₘ ysₒ)


 ++-assoc-split₃ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → ₂′ (╍ (n + m) v₁) ≈ (₂′ ∘ ╍ m ∘ ₂′) (╍ n v₂)
 ++-assoc-split₃ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | ╍ n ys    | ╍ m (₂′ $ ╍ n ys)
 ++-assoc-split₃                        xs≈ys    | xsₙₘ ,′ xsₒ  | ysₙ ,′ ._ | ysₘ ,′ ysₒ =
     ≈-++-suffix {v₁ = xsₙₘ} {ysₙ ++ ysₘ} $ transᵥ xs≈ys (symᵥ $ ++-assoc ysₙ ysₘ ysₒ)


split-++′ : ∀ {n m ℓ} {α : Set ℓ} (v₁ v₁′ : Vec α n) (v₂ v₂′ : Vec α m) → v₁ ++ v₂ ≈ v₁′ ++ v₂′ → v₁ ≈ v₁′ × v₂ ≈ v₂′
split-++′ []       []        _  _   v₂≈v₂′             = []-cong , v₂≈v₂′
split-++′ (_ ∷ xs) (_ ∷ xs′) ys ys′ (_ ∷-cong rest)    with split-++′ xs xs′ ys ys′ rest
split-++′ (_ ∷ _)  (_ ∷ _)   _  _   (x≈x′ ∷-cong rest) | xs≈xs′ , ys≈ys′ = (x≈x′ ∷-cong xs≈xs′) , ys≈ys′

split-++ : ∀ {n m ℓ} {α : Set ℓ} (v₁ v₁′ : Vec α n) (v₂ v₂′ : Vec α m) → v₁ ++ v₂ ≡ v₁′ ++ v₂′ → v₁ ≡ v₁′ × v₂ ≡ v₂′
split-++ v₁ v₁′ v₂ v₂′ p = map to-≡ to-≡ (split-++′ v₁ v₁′ v₂ v₂′ $ from-≡ p)

splitAt-++ : ∀ {ℓ} {α : Set ℓ} {m} n (v₁ : Vec α n) (v₂ : Vec α m) → splitAt n (v₁ ++ v₂) ≡ v₁ , v₂ , refl
splitAt-++ n v₁ v₂ with splitAt n (v₁ ++ v₂)
splitAt-++ n v₁ v₂ | v₁′ , v₂′ , p with split-++ v₁ v₁′ v₂ v₂′ p   | p
splitAt-++ n v₁ v₂ | .v₁ , .v₂ , _ | refl , refl                   | refl = refl
\end{code}
