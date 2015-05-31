\begin{code}
module Data.Vec.Properties.Extra where

open import Function using (_∘_; _$_; id)
open import Data.Nat.Base using (zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Product using (proj₁; _×_; _,_; map)
open import Data.Vec using (Vec; splitAt; _++_; _∷_; []; tabulate; initLast; _∷ʳ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)
open import Data.Vec.Equality using () renaming (module PropositionalEquality to VPE)
open VPE using (_≈_; []-cong; _∷-cong_; from-≡; to-≡) renaming (sym to symᵥ; trans to transᵥ)
open import Data.Vec.Properties using (module UsingVectorEquality)
open module Dummy {a} {A : Set a} = UsingVectorEquality (setoid A) using (xs++[]=xs)

open import Data.Vec.Extra using (proj₂′; ₁; ₂′; initLast′)
\end{code}


%<*proj₁∘splitAt++>
\AgdaTarget{proj₁∘splitAt++}
\begin{code}
proj₁∘splitAt++ : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) → proj₁ (splitAt i₁ (v₁ ++ v₂)) ≡ v₁
proj₁∘splitAt++ {i₁ = zero}  []       _  = refl
proj₁∘splitAt++ {i₁ = suc n} (v ∷ vs) v₂ with splitAt n (vs ++ v₂) | proj₁∘splitAt++ vs v₂
proj₁∘splitAt++ {i₁ = suc n} (v ∷ vs) v₂ | _ , _ , eq              | indH rewrite eq | indH = refl
\end{code}
%</proj₁∘splitAt++>


%<*proj₂′∘splitAt++>
\AgdaTarget{proj₂′∘splitAt++}
\begin{code}
proj₂′∘splitAt++ : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) → proj₂′ (splitAt i₁ (v₁ ++ v₂)) ≡ v₂
proj₂′∘splitAt++ {i₁ = zero}  []       _  = refl
proj₂′∘splitAt++ {i₁ = suc n} (v ∷ vs) v₂ with splitAt n (vs ++ v₂) | proj₂′∘splitAt++ vs v₂
proj₂′∘splitAt++ {i₁ = suc n} (v ∷ vs) v₂ | _ , _ , eq              | indH rewrite eq | indH = refl
\end{code}
%</proj₂′∘splitAt++>


%<*proj₁∘splitAt-last>
\AgdaTarget{proj₁∘splitAt-last}
\begin{code}
proj₁∘splitAt-last : ∀ {ℓ} {α : Set ℓ} {i} (v : Vec α (i + 0)) → proj₁ (splitAt i v) ≈ v
proj₁∘splitAt-last {i = i} v           with splitAt i v
proj₁∘splitAt-last {i = i} .(v′ ++ []) | v′ , [] , refl = symᵥ (xs++[]=xs v′)
\end{code}
%</proj₁∘splitAt-last>


%<*proj₁∘splitAt-last≈>
\AgdaTarget{proj₁∘splitAt-last≈}
\begin{code}
proj₁∘splitAt-last≈ : ∀ {ℓ} {α : Set ℓ} {i} {v : Vec α (i + 0)} {w : Vec α i} → v ≈ w → proj₁ (splitAt i v) ≈ w
proj₁∘splitAt-last≈ {v = v} v≈w = transᵥ (proj₁∘splitAt-last v) v≈w
\end{code}
%</proj₁∘splitAt-last≈>


%<*≈-++-prefix>
\AgdaTarget{≈-++-prefix}
\begin{code}
≈-++-prefix : ∀ {n₁ n₂ ℓ} {α : Set ℓ} {v₁ w₁ : Vec α n₁} {v₂ w₂ : Vec α n₂} → v₁ ++ v₂ ≈ w₁ ++ w₂ → v₁ ≈ w₁
≈-++-prefix {v₁ = []}       {[]}       _                  = []-cong
≈-++-prefix {v₁ = x₁ ∷ xs₁} {y₁ ∷ ys₁} (x≡y ∷-cong xs≈ys) = x≡y ∷-cong (≈-++-prefix xs≈ys)
\end{code}
%</≈-++-prefix>


%<*≈-++-suffix>
\AgdaTarget{≈-++-suffix}
\begin{code}
≈-++-suffix : ∀ {n₁ n₂ ℓ} {α : Set ℓ} {v₁ w₁ : Vec α n₁} {v₂ w₂ : Vec α n₂} → v₁ ++ v₂ ≈ w₁ ++ w₂ → v₂ ≈ w₂
≈-++-suffix {v₁ = []}       {[]}       v₂≈w₂              = v₂≈w₂
≈-++-suffix {v₁ = x₁ ∷ xs₁} {y₁ ∷ ys₁} (x≡y ∷-cong xs≈ys) = ≈-++-suffix {v₁ = xs₁} {ys₁} xs≈ys
\end{code}
%</≈-++-suffix>


%<*++-assoc>
\AgdaTarget{++-assoc}
\begin{code}
++-assoc : ∀ {n₁ n₂ n₃ ℓ} {α : Set ℓ} (v₁ : Vec α n₁) (v₂ : Vec α n₂) (v₃ : Vec α n₃) → (v₁ ++ v₂) ++ v₃ ≈ v₁ ++ (v₂ ++ v₃)
++-assoc []         _ _ = from-≡ refl
++-assoc (x₁ ∷ xs₁) _ _ = refl ∷-cong (++-assoc xs₁ _ _)
\end{code}
%</++-assoc>


\begin{code}
module _ where
 pattern _,′_ left right = left , right , refl
 private ╍ = splitAt
\end{code}

%<*++-assoc-split₁>
\AgdaTarget{++-assoc-split₁}
\begin{code}
 ++-assoc-split₁ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → (₁ ∘ ╍ n ∘ ₁) (╍ (n + m) v₁) ≈ ₁ (╍ n v₂)
 ++-assoc-split₁ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | (╍ n ∘ ₁) (╍ (n + m) xs) | ╍ n ys
 ++-assoc-split₁                        xs≈ys |    ._ ,′ xsₒ    | xsₙ ,′ xsₘ               | _ ,′ _ =
     ≈-++-prefix $ transᵥ (symᵥ $ ++-assoc xsₙ xsₘ xsₒ) xs≈ys
\end{code}
%</++-assoc-split₁>
 
%<*++-assoc-split₂>
\AgdaTarget{++-assoc-split₂}
\begin{code}
 ++-assoc-split₂ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → (₂′ ∘ ╍ n ∘ ₁) (╍ (n + m) v₁) ≈ (₁ ∘ ╍ m ∘ ₂′) (╍ n v₂)
 ++-assoc-split₂ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | (╍ n ∘ ₁) (╍ (n + m) xs) | ╍ n ys    | (╍ m ∘ ₂′) (╍ n ys)
 ++-assoc-split₂                        xs≈ys | ._ ,′ _         | xsₙ ,′ _                 | ysₙ ,′ ._ | ysₘ ,′ ysₒ =
     ≈-++-suffix {v₁ = xsₙ} {ysₙ} $ ≈-++-prefix $ transᵥ xs≈ys (symᵥ $ ++-assoc ysₙ ysₘ ysₒ)
\end{code}
%</++-assoc-split₂>

%<*++-assoc-split₃>
\AgdaTarget{++-assoc-split₃}
\begin{code}
 ++-assoc-split₃ : ∀ {n m o ℓ} {α : Set ℓ} {v₁ : Vec α ((n + m) + o)} {v₂ : Vec α (n + (m + o))}
                   → v₁ ≈ v₂ → ₂′ (╍ (n + m) v₁) ≈ (₂′ ∘ ╍ m ∘ ₂′) (╍ n v₂)
 ++-assoc-split₃ {n} {m} {v₁ = xs} {ys} xs≈ys with ╍ (n + m) xs | ╍ n ys    | ╍ m (₂′ $ ╍ n ys)
 ++-assoc-split₃                        xs≈ys | xsₙₘ ,′ xsₒ     | ysₙ ,′ ._ | ysₘ ,′ ysₒ =
     ≈-++-suffix {v₁ = xsₙₘ} {ysₙ ++ ysₘ} $ transᵥ xs≈ys (symᵥ $ ++-assoc ysₙ ysₘ ysₒ)
\end{code}
%</++-assoc-split₃>


%<*split-++′>
\AgdaTarget{split-++′}
\begin{code}
split-++′ : ∀ {n m ℓ} {α : Set ℓ} (v₁ v₁′ : Vec α n) (v₂ v₂′ : Vec α m) → v₁ ++ v₂ ≈ v₁′ ++ v₂′ → v₁ ≈ v₁′ × v₂ ≈ v₂′
split-++′ []       []        _  _   v₂≈v₂′             = []-cong , v₂≈v₂′
split-++′ (_ ∷ xs) (_ ∷ xs′) ys ys′ (_    ∷-cong rest) with split-++′ xs xs′ ys ys′ rest
split-++′ (_ ∷ _)  (_ ∷ _)   _  _   (x≈x′ ∷-cong rest) | xs≈xs′ , ys≈ys′ = (x≈x′ ∷-cong xs≈xs′) , ys≈ys′
\end{code}
%</split-++′>


%<*split-++>
\AgdaTarget{split-++}
\begin{code}
split-++ : ∀ {n m ℓ} {α : Set ℓ} (v₁ v₁′ : Vec α n) (v₂ v₂′ : Vec α m) → v₁ ++ v₂ ≡ v₁′ ++ v₂′ → v₁ ≡ v₁′ × v₂ ≡ v₂′
split-++ v₁ v₁′ v₂ v₂′ p = map to-≡ to-≡ (split-++′ v₁ v₁′ v₂ v₂′ $ from-≡ p)
\end{code}
%</split-++>


%<*splitAt-++>
\AgdaTarget{splitAt-++}
\begin{code}
splitAt-++ : ∀ {ℓ} {α : Set ℓ} {m} n (v₁ : Vec α n) (v₂ : Vec α m) → splitAt n (v₁ ++ v₂) ≡ (v₁ , (v₂ , refl))
splitAt-++ n v₁ v₂ with splitAt n (v₁ ++ v₂)
splitAt-++ n v₁ v₂ | v₁′ , v₂′ , p with split-++ v₁ v₁′ v₂ v₂′ p   | p
splitAt-++ n v₁ v₂ | .v₁ , .v₂ , _ | refl , refl                   | refl = refl
\end{code}
%</splitAt-++>


%<*tabulate-ext>
\AgdaTarget{tabulate-ext}
\begin{code}
tabulate-ext : ∀ {ℓ n} {α : Set ℓ} {f g : Fin n → α} → (∀ x → f x ≡ g x) → tabulate f ≡ tabulate g
tabulate-ext {n = zero}  _ = refl
tabulate-ext {n = suc m} p rewrite p Fz | tabulate-ext (p ∘ Fs) = refl
\end{code}
%</tabulate-ext>


%<*drop-initLast-noproof>
\AgdaTarget{drop-initLast′}
\begin{code}
drop-initLast′ : ∀ {ℓ n} {α : Set ℓ} (x : α) (xs : Vec α (suc n)) → initLast′ (x ∷ xs) ≡ map (x ∷_) id (initLast′ xs)
drop-initLast′ _ xs         with initLast xs
drop-initLast′ _ .(ys ∷ʳ y) | ys , y , refl = refl
\end{code}
%</drop-initLast-noproof>
