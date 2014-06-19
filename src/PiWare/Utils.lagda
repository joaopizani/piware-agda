\begin{code}
module PiWare.Utils where

open import Function using (_$_; _∘_)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.List using (List; gfilter; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _≤_; _≥_; z≤n; s≤s)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
\end{code}

\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} → {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((a , b) ∷ xs) = let (as , bs) = unzip xs in (a ∷ as , b ∷ bs)
\end{code}

%<*splitSumList>
\begin{code}
splitSumList : ∀ {α β} → List (α ⊎ β) → List α × List β
splitSumList = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</splitSumList>

%<*notLEQtoGEQ>
\begin{code}
notLEQtoGEQ : {n m : ℕ} → ¬ (suc n ≤ m) → (n ≥ m)
notLEQtoGEQ {_}     {zero}  _  = z≤n
notLEQtoGEQ {zero}  {suc m} ¬p = contradiction (s≤s z≤n) ¬p
notLEQtoGEQ {suc n} {suc m} ¬p = s≤s $ notLEQtoGEQ (¬p ∘ s≤s)
\end{code}
%</notLEQtoGEQ>
