\begin{code}
module PiWare.Utils where

open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.List using (List; gfilter; _∷_; [])
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
