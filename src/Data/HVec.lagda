\begin{code}
open import Level using (_⊔_; Level) renaming (suc to lsuc)

open import Function using (_$_; _∘_; id)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; #_) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (true) renaming (Bool to B)
open import Data.Vec using (Vec; replicate; lookup; [_]; _++_; zipWith; _⊛_; last) renaming ([] to ε; _∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}


-- Type-heterogenenous vectors.
-- The "↑" in the name is pronounced "lifted", because these vectors are INDEXED by a vector of TYPES.
\begin{code}
infixr 30 _◁̂_

data Vec↑ {ℓ} : ∀ n → Vec (Set ℓ) n → Set (lsuc ℓ) where
    ε̂   : Vec↑ 0 ε
    _◁̂_ : ∀ {α : Set ℓ} {k} {αs} → α → Vec↑ k αs → Vec↑ (suc k) (α ◁ αs)
\end{code}


-- Index-heterogeneous vectors
-- The "↑′" is pronouced "index-lifted", as these vectors are INDEXED by a vector of INDICES.
\begin{code}
infixr 30 _◁′_

data Vec↑′ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → Set ℓ₂) : ∀ n → Vec I n → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    ε′   :                                   Vec↑′ C 0 ε
    _◁′_ : ∀ {k i is} → C i → Vec↑′ C k is → Vec↑′ C (suc k) (i ◁ is)
\end{code}


-- Index-related-heterogeneous vectors
\begin{code}
record ⊤′ {ℓ} : Set ℓ where constructor tt′  -- Universe-polymorphic Unit

_◁?_ : ∀ {ℓ n} {I : Set ℓ} → I → Vec I n → Set ℓ
_ ◁? ε        = ⊤′
x ◁? (y ◁ ys) = x ≡ y

_⧺?_ : ∀ {ℓ m n} {I : Set ℓ} → Vec I m → Vec I n → Set ℓ
ε        ⧺? _  = ⊤′
(x ◁ xs) ⧺? ys = last (x ◁ xs) ◁? ys

postulate tail-⧺? : ∀ {m n ℓ} {I : Set ℓ} {x : I} {xs : Vec I m} {ys : Vec I n} → (x ◁ xs) ⧺? ys → xs ⧺? ys

-- This maybe not true? Maybe a more specific version...
postulate concat-◁? : ∀ {m n ℓ} {I : Set ℓ} {x : I} {xs : Vec I m} {ys : Vec I n} → x ◁? xs → x ◁? (xs ++ ys)


infixr 30 _◁⁼[_]_

data Vec↑⁼ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → I → Set ℓ₂) : ∀ n (is os : Vec I n) → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    ε⁼   : Vec↑⁼ C 0 ε ε
    _◁⁼[_]_ : ∀ {n i₀ o₀ is os} → C i₀ o₀ → o₀ ◁? is → Vec↑⁼ C n is os → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os)
\end{code}


\begin{code}
lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (k : Fin n) → Vec↑ n αs → lookup k αs
lookup↑ Fz     (x ◁̂ _)  = x
lookup↑ (Fs k) (_ ◁̂ xs) = lookup↑ k xs

lookup↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I n} (k : Fin n) → Vec↑′ C n is → C (lookup k is)
lookup↑′ Fz     (x ◁′ _)  = x
lookup↑′ (Fs k) (_ ◁′ xs) = lookup↑′ k xs

lookup↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {is os : Vec I n} (k : Fin n) → Vec↑⁼ C n is os → C (lookup k is) (lookup k os)
lookup↑⁼ Fz     (x ◁⁼[ _ ] _)  = x
lookup↑⁼ (Fs k) (_ ◁⁼[ _ ] xs) = lookup↑⁼ k xs
\end{code}


\begin{code}
head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x

head↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → C i
head↑′ (x ◁′ _) = x

head↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} {is os : Vec I n} → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os) → C i₀ o₀
head↑⁼ (x ◁⁼[ _ ] _) = x
\end{code}


\begin{code}
tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs

tail↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → Vec↑′ C n is
tail↑′ (_ ◁′ xs) = xs

tail↑⁼ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} {is os : Vec I n} → Vec↑⁼ C (suc n) (i₀ ◁ is) (o₀ ◁ os) → Vec↑⁼ C n is os
tail↑⁼ (_ ◁⁼[ _ ] xs) = xs
\end{code}


\begin{code}
[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂

[_]↑′ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} → C i → Vec↑′ C 1 [ i ]
[ x ]↑′ = x ◁′ ε′

[_]↑⁼ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {i₀ o₀ : I} → C i₀ o₀ → Vec↑⁼ C 1 [ i₀ ] [ o₀ ]
[ x ]↑⁼ = x ◁⁼[ _ ] ε⁼
\end{code}


\begin{code}
infixr 5 _⧺↑_

_⧺↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ⧺↑ ys = ys
(x ◁̂ xs) ⧺↑ ys = x ◁̂ (xs ⧺↑ ys)

infixr 5 _⧺↑′_

_⧺↑′_ : ∀ {m n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I m} {js : Vec I n} → Vec↑′ C m is → Vec↑′ C n js → Vec↑′ C (m + n) (is ++ js)
ε′        ⧺↑′ ys = ys
(x ◁′ xs) ⧺↑′ ys = x ◁′ (xs ⧺↑′ ys)

infixr 5 _⧺↑⁼_

_⧺↑⁼_ : ∀ {m n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → I → Set ℓ₂} {is₁ os₁ : Vec I m} {is₂ os₂ : Vec I n}
        → Vec↑⁼ C m is₁ os₁ → Vec↑⁼ C n is₂ os₂ → {p : os₁ ⧺? is₂} → Vec↑⁼ C (m + n) (is₁ ++ is₂) (os₁ ++ os₂)
ε⁼ ⧺↑⁼ ys = ys
_⧺↑⁼_ {os₁ = (o₁ ◁ os₁)} {is₂ = is₂} (x ◁⁼[ p◁? ] xs) ys {p⧺?} = x ◁⁼[ concat-◁? p◁? ] (_⧺↑⁼_ xs ys {tail-⧺? {xs = os₁} {ys = is₂} p⧺?})
\end{code}


\begin{code}
infixr 3 _⊛⇒_

_⊛⇒_ : ∀ {n ℓ} → Vec (Set ℓ) n → Vec (Set ℓ) n → Vec (Set ℓ) n
ε        ⊛⇒ ε        = ε
(α ◁ αs) ⊛⇒ (β ◁ βs) = (α → β) ◁ (αs ⊛⇒ βs)
\end{code}


\begin{code}
infixr 4 _⊛↑_

_⊛↑_ : ∀ {n ℓ} {αs βs : Vec (Set ℓ) n} → Vec↑ n (αs ⊛⇒ βs) → Vec↑ n αs → Vec↑ n βs
_⊛↑_ {αs = ε}      {ε}      ε̂        ε̂        = ε̂
_⊛↑_ {αs = α ◁ αs} {β ◁ βs} (f ◁̂ fs) (x ◁̂ xs) = f x ◁̂ (fs ⊛↑ xs)
\end{code}


\begin{code}
replicate↑ : ∀ {ℓ} {α : Set ℓ} {n} → α → Vec↑ n (replicate α)
replicate↑ {n = zero}   _ = ε̂
replicate↑ {n = suc n′} x = x ◁̂ replicate↑ x
\end{code}


-- TODO: implement map↑ using pure↑ (replicate↑) and ⊛↑
\begin{code}
map↑ : ∀ {n ℓ} {α β : Set ℓ} → (α → β) → Vec↑ n (replicate α) → Vec↑ n (replicate β)
map↑ f ε̂        = ε̂
map↑ f (x ◁̂ xs) = f x ◁̂ map↑ f xs


map↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i j : I} → (C i → C j) → Vec↑′ C n (replicate i) → Vec↑′ C n (replicate j)
map↑′ f ε′        = ε′
map↑′ f (x ◁′ xs) = f x ◁′ map↑′ f xs
\end{code}



\begin{code}
test1Vec↑ : Vec↑ 2 (ℕ ◁ B ◁ ε)
test1Vec↑ = 3 ◁̂ true ◁̂ ε̂
\end{code}

\begin{code}
test2Vec↑ : Vec↑ 3 (replicate Set)
test2Vec↑ = ℕ ◁̂ B ◁̂ ℕ ◁̂ ε̂
\end{code}

\begin{code}
test3Vec↑ : Vec↑ 3 (replicate Set₁)
test3Vec↑ = Set ◁̂ Set ◁̂ Set ◁̂ ε̂
\end{code}

\begin{code}
test1Vec↑′ : Vec↑′ Fin _ (1 ◁ 2 ◁ 3 ◁ ε)
test1Vec↑′ = (# 0) ◁′ (# 1) ◁′ (# 2) ◁′ ε′
\end{code}

\begin{code}
postulate ℂ : ℕ → ℕ → Set
postulate Gate : ∀ i o → ℂ i o

test1Vec↑⁼ : Vec↑⁼ ℂ _ (1 ◁ 5 ◁ 2 ◁ ε) (5 ◁ 2 ◁ 3 ◁ ε)
test1Vec↑⁼ = Gate 1 5 ◁⁼[ refl ] Gate 5 2 ◁⁼[ refl ] Gate 2 3 ◁⁼[ tt′ ] ε⁼
\end{code}
