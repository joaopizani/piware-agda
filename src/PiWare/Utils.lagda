\begin{code}
module PiWare.Utils where

open import Function using (id)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; proj₁; <_,_>; map)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.Vec using (Vec; splitAt)
open import Data.List using (List; gfilter; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
\end{code}


%<*unzip>
\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((x , y) ∷ zs) = map (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip>

%<*unzip-nonempty>
\begin{code}
unzip⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List⁺ (α × β) → List⁺ α × List⁺ β
unzip⁺ ((x , y) ∷ zs) = map (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip-nonempty>


%<*uncurry-nonempty>
\begin{code}
uncurry⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {γ : Set ℓ₂} → (α → List α → γ) → List⁺ α → γ
uncurry⁺ f (x ∷ xs) = f x xs
\end{code}
%</uncurry-nonempty>


%<*splitAt-noproof>
\begin{code}
splitAt' : ∀ {ℓ} {α : Set ℓ} (m : ℕ) {n : ℕ} → Vec α (m + n) → Vec α m × Vec α n
splitAt' m v = map id proj₁ (splitAt m v)
\end{code}
%</splitAt-noproof>

%<*splitAt-nonempty>
\begin{code}
splitAt⁺ : ∀ {ℓ} {α : Set ℓ} (m : ℕ) {n : ℕ} → List⁺ (Vec α (m + n)) → List⁺ (Vec α m × Vec α n)
splitAt⁺ m = map⁺ (splitAt' m)
\end{code}
%</splitAt-nonempty>


%<*seggregateSums>
\begin{code}
seggregateSums : ∀ {ℓ} {α β : Set ℓ} → List (α ⊎ β) → List α × List β
seggregateSums = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</seggregateSums>
