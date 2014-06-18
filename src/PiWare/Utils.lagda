\begin{code}
module PiWare.Utils where

open import Data.Product using (_×_; <_,_>)
open import Data.Sum using (_⊎_; isInj₁; isInj₂)
open import Data.List using (List; gfilter)
\end{code}

%<*splitSumList>
\begin{code}
splitSumList : ∀ {α β} → List (α ⊎ β) → List α × List β
splitSumList = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</splitSumList>
