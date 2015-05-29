\begin{code}
module Data.IVec where

open import Level using (_⊔_) renaming (suc to lsuc)

open import Data.Nat.Base using (suc; _+_)
open import Data.Fin using (Fin; #_) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; lookup; [_]; _++_; replicate) renaming ([] to ε; _∷_ to _◁_)
\end{code}


-- Index-heterogeneous vectors
-- The "↑′" is pronouced "index-lifted", as these vectors are INDEXED by a vector of INDICES.
\begin{code}
infixr 30 _◁′_

data Vec↑′ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → Set ℓ₂) : ∀ n → Vec I n → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    ε′   :                                   Vec↑′ C 0 ε
    _◁′_ : ∀ {k i is} → C i → Vec↑′ C k is → Vec↑′ C (suc k) (i ◁ is)
\end{code}


\begin{code}
lookup↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I n} (k : Fin n) → Vec↑′ C n is → C (lookup k is)
lookup↑′ Fz     (x ◁′ _)  = x
lookup↑′ (Fs k) (_ ◁′ xs) = lookup↑′ k xs
\end{code}


\end{code}
head↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → C i
head↑′ (x ◁′ _) = x
\end{code}


\begin{code}
tail↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → Vec↑′ C n is
tail↑′ (_ ◁′ xs) = xs
\end{code}


\begin{code}
[_]↑′ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} → C i → Vec↑′ C 1 [ i ]
[ x ]↑′ = x ◁′ ε′
\end{code}


\begin{code}
infixr 5 _⧺↑′_

_⧺↑′_ : ∀ {m n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I m} {js : Vec I n} → Vec↑′ C m is → Vec↑′ C n js → Vec↑′ C (m + n) (is ++ js)
ε′        ⧺↑′ ys = ys
(x ◁′ xs) ⧺↑′ ys = x ◁′ (xs ⧺↑′ ys)
\end{code}


\begin{code}
map↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i j : I} → (C i → C j) → Vec↑′ C n (replicate i) → Vec↑′ C n (replicate j)
map↑′ f ε′        = ε′
map↑′ f (x ◁′ xs) = f x ◁′ map↑′ f xs
\end{code}


\begin{code}
test1Vec↑′ : Vec↑′ Fin _ (1 ◁ 2 ◁ 3 ◁ ε)
test1Vec↑′ = (# 0) ◁′ (# 1) ◁′ (# 2) ◁′ ε′
\end{code}
