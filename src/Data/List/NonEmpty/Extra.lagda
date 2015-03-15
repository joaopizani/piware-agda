\begin{code}
module Data.List.NonEmpty.Extra where

open import Data.Nat using (_+_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺; [_] to [_]⁺)
open import Data.Product using (_×_; _,_; map)
open import Data.List.Extra using (unzip)
open import Data.Vec using (Vec)
open import Data.Vec.Extra using (splitAt′)
\end{code}


%<*unzip-nonempty>
\AgdaTarget{unzip⁺}
\begin{code}
unzip⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List⁺ (α × β) → List⁺ α × List⁺ β
unzip⁺ ((x , y) ∷ zs) = map (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip-nonempty>


%<*uncurry-nonempty>
\AgdaTarget{uncurry⁺}
\begin{code}
uncurry⁺ : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {γ : Set ℓ₂} → (α → List α → γ) → List⁺ α → γ
uncurry⁺ f (x ∷ xs) = f x xs
\end{code}
%</uncurry-nonempty>


%<*splitAt-nonempty>
\AgdaTarget{splitAt⁺}
\begin{code}
splitAt⁺ : ∀ {ℓ} {α : Set ℓ} m {n} → List⁺ (Vec α (m + n)) → List⁺ (Vec α m × Vec α n)
splitAt⁺ m = map⁺ (splitAt′ m)
\end{code}
%</splitAt-nonempty>


-- Needs to use the trick with tails⁺' and uncurry⁺ to "convince" the termination checker
%<*tails-nonempty>
\AgdaTarget{tails⁺}
\begin{code}
tails⁺ : ∀ {ℓ} {α : Set ℓ} → List⁺ α → List⁺ (List⁺ α)
tails⁺ {α} = uncurry⁺ tails⁺'
  where tails⁺' : ∀ {ℓ} {α : Set ℓ} → α → List α → List⁺ (List⁺ α)
        tails⁺' x₀ []        = [ x₀ ∷ [] ]⁺
        tails⁺' x₀ (x₁ ∷ xs) = let (t₁ ∷ ts) = tails⁺' x₁ xs  in  (x₀ ∷ x₁ ∷ xs) ∷ (t₁ ∷ ts)
\end{code}
%</tails-nonempty>
