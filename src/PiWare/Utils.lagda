\begin{code}
module PiWare.Utils where

open import Function using (id)
open import Data.Product using (_×_; _,_; proj₁; <_,_>) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.Vec using (Vec; splitAt)
open import Data.List using (List; gfilter; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.Nat using (ℕ; zero; suc; _+_)
\end{code}


%<*unzip>
\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} → {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((x , y) ∷ zs) = let (xs , ys) = unzip zs in (x ∷ xs , y ∷ ys)
\end{code}
%</unzip>

%<*unzip-nonempty>
\begin{code}
unzip⁺ : ∀ {ℓ₁ ℓ₂} → {α : Set ℓ₁} {β : Set ℓ₂} → List⁺ (α × β) → List⁺ α × List⁺ β
unzip⁺ ((x , y) ∷ zs) = let (xs , ys) = unzip zs in (x ∷ xs , y ∷ ys)
\end{code}
%</unzip-nonempty>


%<*splitAt-noproof>
\begin{code}
splitAt' : {α : Set} (m : ℕ) {n : ℕ} → Vec α (m + n) → Vec α m × Vec α n
splitAt' m v = mapₚ id proj₁ (splitAt m v)
\end{code}
%</splitAt-noproof>

%<*splitAt-nonempty>
\begin{code}
splitAt⁺ : {α : Set} (m : ℕ) {n : ℕ} → List⁺ (Vec α (m + n)) → List⁺ (Vec α m × Vec α n)
splitAt⁺ m = map⁺ (splitAt' m)
\end{code}
%</splitAt-nonempty>

%<*seggregateSums>
\begin{code}
seggregateSums : {α β : Set} → List (α ⊎ β) → List α × List β
seggregateSums = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</seggregateSums>
