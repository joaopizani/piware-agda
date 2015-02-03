\begin{code}
module PiWare.Utils where

open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.Vec using (Vec; splitAt; _++_; group) renaming ([] to ε; _∷_ to _◁_)
open import Data.List using (List; gfilter; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


%<*unzip>
\AgdaTarget{unzip}
\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((x , y) ∷ zs) = mapₚ (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip>

%<*unzip-nonempty>
\AgdaTarget{unzip⁺}
\begin{code}
unzip⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List⁺ (α × β) → List⁺ α × List⁺ β
unzip⁺ ((x , y) ∷ zs) = mapₚ (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip-nonempty>


%<*uncurry-nonempty>
\AgdaTarget{uncurry⁺}
\begin{code}
uncurry⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {γ : Set ℓ₂} → (α → List α → γ) → List⁺ α → γ
uncurry⁺ f (x ∷ xs) = f x xs
\end{code}
%</uncurry-nonempty>


%<*splitAt-noproof>
\AgdaTarget{splitAt'}
\begin{code}
splitAt' : ∀ {ℓ} {α : Set ℓ} (m : ℕ) {n : ℕ} → Vec α (m + n) → Vec α m × Vec α n
splitAt' m v = mapₚ id proj₁ (splitAt m v)
\end{code}
%</splitAt-noproof>

%<*group-noproof>
\AgdaTarget{group'}
\begin{code}
group' : ∀ {ℓ} {α : Set ℓ} (n k : ℕ) → Vec α (n * k) → Vec (Vec α k) n
group' n k = proj₁ ∘ group n k
\end{code}
%</group-noproof>

%<*splitAt-nonempty>
\AgdaTarget{splitAt⁺}
\begin{code}
splitAt⁺ : ∀ {ℓ} {α : Set ℓ} (m : ℕ) {n : ℕ} → List⁺ (Vec α (m + n)) → List⁺ (Vec α m × Vec α n)
splitAt⁺ m = map⁺ (splitAt' m)
\end{code}
%</splitAt-nonempty>


%<*seggregateSums>
\AgdaTarget{seggregateSums}
\begin{code}
seggregateSums : ∀ {ℓ} {α β : Set ℓ} → List (α ⊎ β) → List α × List β
seggregateSums = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</seggregateSums>


%<*lemma-proj₁-splitAt>
\begin{code}
lemma-proj₁-splitAt : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂)
                      → proj₁ (splitAt i₁ (v₁ ++ v₂)) ≡ v₁
lemma-proj₁-splitAt {i₁ = zero}  ε        v₂ = refl
lemma-proj₁-splitAt {i₁ = suc n} (v ◁ vs) v₂ with splitAt n (vs ++ v₂) | lemma-proj₁-splitAt vs v₂
lemma-proj₁-splitAt {i₁ = suc n} (v ◁ vs) v₂ | _ , _ , eq              | ind rewrite eq | ind = refl
\end{code}
%</lemma-proj₁-splitAt>

%<*lemma-proj₁₂-splitAt>
\begin{code}
lemma-proj₁₂-splitAt : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) 
                       → proj₁ (proj₂ (splitAt i₁ (v₁ ++ v₂))) ≡ v₂
lemma-proj₁₂-splitAt {i₁ = zero}  ε        _  = refl
lemma-proj₁₂-splitAt {i₁ = suc n} (v ◁ vs) v₂ with splitAt n (vs ++ v₂) | lemma-proj₁₂-splitAt vs v₂
lemma-proj₁₂-splitAt {i₁ = suc n} (v ◁ vs) v₂ | _ , _ , eq              | ind rewrite eq | ind = refl
\end{code}
%</lemma-proj₁₂-splitAt>
