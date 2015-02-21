\begin{code}
module Data.List.Extra where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; map)
\end{code}


%<*unzip>
\AgdaTarget{unzip}
\begin{code}
unzip : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → List (α × β) → List α × List β
unzip []             = [] , []
unzip ((x , y) ∷ zs) = map (_∷_ x) (_∷_ y) (unzip zs)
\end{code}
%</unzip>
