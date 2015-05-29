\begin{code}
module Data.RVec where

open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)

open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; lookup; last; _++_; [_]) renaming ([] to ε; _∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


-- Index-related-heterogeneous vectors
\begin{code}
_◁?_ : ∀ {ℓ n} {I : Set ℓ} → I → Vec I n → Set ℓ
_ ◁? ε        = Lift ⊤
x ◁? (y ◁ ys) = x ≡ y

_⧺?_ : ∀ {ℓ m n} {I : Set ℓ} → Vec I m → Vec I n → Set ℓ
ε        ⧺? _  = Lift ⊤
(x ◁ xs) ⧺? ys = last (x ◁ xs) ◁? ys

postulate last∘◁ : ∀ {n ℓ} {α : Set ℓ} (x : α) (xs : Vec α (suc n)) → last (x ◁ xs) ≡ last xs
--last∘◁ x (y ◁ ε) = refl
--last∘◁ x (y ◁ z ◁ zs)         with initLast (x ◁ y ◁ z ◁ zs)
--last∘◁ x (y ◁ z ◁ .ε)         | (.x ◁ .y ◁ ε)       , .z , refl = refl
--last∘◁ x (y ◁ z ◁ .(zs ∷ʳ l)) | (.x ◁ .y ◁ .z ◁ zs) , l  , refl = {!!}

tail-⧺ : ∀ {m n ℓ} {I : Set ℓ} {x : I} {xs : Vec I m} {ys : Vec I n} → (x ◁ xs) ⧺? ys → xs ⧺? ys
tail-⧺ {x = _} {xs = ε}      _ = lift tt
tail-⧺ {x = x} {xs = z ◁ zs} p rewrite last∘◁ x (z ◁ zs) = p

-- This maybe not true? Maybe a more specific version...
postulate concat-◁ : ∀ {m n ℓ} {I : Set ℓ} {x : I} {xs : Vec I m} {ys : Vec I n} → x ◁? xs → x ◁? (xs ++ ys)


infixr 30 _◁⁼[_]_

data Vec↑⁼ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → I → Set ℓ₂) : ∀ n (is os : Vec I n) → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    ε⁼      : Vec↑⁼ C 0 ε ε
    _◁⁼[_]_ : ∀ {n i₀ o₀ is os} → C i₀ o₀ → o₀ ◁? is → Vec↑⁼ C n is os → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os)
\end{code}


\begin{code}
lookup↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {is os : Vec I n} (k : Fin n) → Vec↑⁼ C n is os → C (lookup k is) (lookup k os)
lookup↑⁼ Fz     (x ◁⁼[ _ ] _)  = x
lookup↑⁼ (Fs k) (_ ◁⁼[ _ ] xs) = lookup↑⁼ k xs
\end{code}


\begin{code}
head↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} {is os : Vec I n} → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os) → C i₀ o₀
head↑⁼ (x ◁⁼[ _ ] _) = x
\end{code}


\begin{code}
tail↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} {is os : Vec I n} → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os) → Vec↑⁼ C n is os
tail↑⁼ (_ ◁⁼[ _ ] xs) = xs
\end{code}


\begin{code}
[_]↑⁼ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} → C i₀ o₀ → Vec↑⁼ C 1 [ i₀ ] [ o₀ ]
[ x ]↑⁼ = x ◁⁼[ _ ] ε⁼
\end{code}


\begin{code}
infixr 5 _⧺↑⁼_

_⧺↑⁼_ : ∀ {m n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {is₁ os₁ : Vec I m} {is₂ os₂ : Vec I n} → Vec↑⁼ C m is₁ os₁ → Vec↑⁼ C n is₂ os₂ → {p : os₁ ⧺? is₂} → Vec↑⁼ C (m + n) (is₁ ++ is₂) (os₁ ++ os₂)
_⧺↑⁼_ {m = 0}      {n = n′}     ε⁼ ys = ys
_⧺↑⁼_ {m = suc m′} {n = 0}      (x ◁⁼[ x◁? ] xs) ε⁼               = {!!}
_⧺↑⁼_ {m = suc m′} {n = suc n′} (x ◁⁼[ x◁? ] xs) (y ◁⁼[ y◁? ] ys) = {!!}
\end{code}


\begin{code}
postulate ℂ : ℕ → ℕ → Set
postulate Gate : ∀ i o → ℂ i o

test1Vec↑⁼ : Vec↑⁼ ℂ _ (1 ◁ 5 ◁ 2 ◁ ε) (5 ◁ 2 ◁ 3 ◁ ε)
test1Vec↑⁼ = Gate 1 5 ◁⁼[ refl ] Gate 5 2 ◁⁼[ refl ] Gate 2 3 ◁⁼[ lift tt ] ε⁼
\end{code}
