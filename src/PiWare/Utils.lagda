\begin{code}
module PiWare.Utils where

open import Function using (_$_; _∘_; id)
open import Data.Product using (_×_; _,_; proj₁; <_,_>) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.Vec using (Vec; splitAt)
open import Data.List using (List; gfilter; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≥_; z≤n; s≤s; _+_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
\end{code}


%<*unzip>
\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} → {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((a , b) ∷ xs) = let (as , bs) = unzip xs in (a ∷ as , b ∷ bs)
\end{code}
%</unzip>

%<*unzip-nonempty>
\begin{code}
unzip⁺ : ∀ {ℓ₁ ℓ₂} → {α : Set ℓ₁} {β : Set ℓ₂} → List⁺ (α × β) → List⁺ α × List⁺ β
unzip⁺ ((a , b) ∷ xs) = let (as , bs) = unzip xs in (a ∷ as , b ∷ bs)
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

%<*segregateSums>
\begin{code}
segregateSums : {α β : Set} → List (α ⊎ β) → List α × List β
segregateSums = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</segregateSums>

%<*notLEQtoGEQ>
\begin{code}
notLEQtoGEQ : {n m : ℕ} → ¬ (suc n ≤ m) → (n ≥ m)
notLEQtoGEQ {_}     {zero}  _  = z≤n
notLEQtoGEQ {zero}  {suc m} ¬p = contradiction (s≤s z≤n) ¬p
notLEQtoGEQ {suc n} {suc m} ¬p = s≤s $ notLEQtoGEQ (¬p ∘ s≤s)
\end{code}
%</notLEQtoGEQ>
