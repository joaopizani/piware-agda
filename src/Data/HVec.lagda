\begin{code}
open import Level using (_⊔_) renaming (suc to lsuc)

open import Function using (_$_; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (true) renaming (Bool to B)
open import Data.Vec using (Vec; replicate; lookup; [_]; _++_; zipWith; _⊛_) renaming ([] to ε; _∷_ to _◁_)

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
    _◁′_ : ∀ {i k is} → C i → Vec↑′ C k is → Vec↑′ C (suc k) (i ◁ is)
\end{code}


-- Index-aligned-heterogeneous vectors
-- Besides being indexed by a vector of INDICES, there is an additional constraint:
-- Each element in the indexing vector must be propositionally equal to its predecessor.
\begin{code}
infixr 30 _◁⁼_

data Vec↑⁼ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → I → Set ℓ₂) : ∀ n → Vec I n → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    [_]⁼ : ∀ {i₀ i₁}          → C i₀ i₁ → Vec↑⁼ C 1 [ i₀ ]
    _◁⁼_ : ∀ {i₀ i₁ i₁′ k is} → C i₀ i₁ → Vec↑⁼ C (suc k) (i₁′ ◁ is) → {eq : i₁ ≡ i₁′}
                                        → Vec↑⁼ C (suc (suc k)) (i₀ ◁ i₁ ◁ is)
\end{code}


\begin{code}
lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (k : Fin n) → Vec↑ n αs → lookup k αs
lookup↑ Fz     (x ◁̂ _)  = x
lookup↑ (Fs k) (_ ◁̂ xs) = lookup↑ k xs

lookup↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I n} (k : Fin n) → Vec↑′ C n is → C (lookup k is)
lookup↑′ Fz     (x ◁′ _)  = x
lookup↑′ (Fs k) (_ ◁′ xs) = lookup↑′ k xs
\end{code}


\begin{code}
head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x

head↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → C i
head↑′ (x ◁′ _) = x
\end{code}


\begin{code}
tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs

tail↑′ : ∀ {n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} {is : Vec I n} → Vec↑′ C (suc n) (i ◁ is) → Vec↑′ C n is
tail↑′ (_ ◁′ xs) = xs
\end{code}


\begin{code}
[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂

[_]↑′ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {i : I} → C i → Vec↑′ C 1 [ i ]
[ x ]↑′ = x ◁′ ε′
\end{code}


\begin{code}
infixr 5 _++↑_

_++↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ++↑ ys = ys
(x ◁̂ xs) ++↑ ys = x ◁̂ (xs ++↑ ys)

infixr 5 _++↑′_

_++↑′_ : ∀ {m n ℓ₁ ℓ₂} {I : Set ℓ₁} {C : I → Set ℓ₂} {is : Vec I m} {js : Vec I n} → Vec↑′ C m is → Vec↑′ C n js → Vec↑′ C (m + n) (is ++ js)
ε′        ++↑′ ys = ys
(x ◁′ xs) ++↑′ ys = x ◁′ (xs ++↑′ ys)
\end{code}


\begin{code}
infixr 3 _⊛⇒_

_⊛⇒_ : ∀ {n ℓ} → Vec (Set ℓ) n → Vec (Set ℓ) n → Vec (Set ℓ) n
_⊛⇒_ = zipWith (λ α β → (α → β))
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


\begin{code}
postulate map↑ : ∀ {n ℓ} {α β : Set ℓ} → (α → β) → Vec↑ n (replicate α) → Vec↑ n (replicate β)
\end{code}



\begin{code}
test1Vec↑ : Vec↑ _ (ℕ ◁ B ◁ ε)
test1Vec↑ = 3 ◁̂ true ◁̂ ε̂
\end{code}

\begin{code}
test2Vec↑ : Vec↑ _ (replicate Set)
test2Vec↑ = ℕ ◁̂ B ◁̂ ℕ ◁̂ ε̂
\end{code}

\begin{code}
test3Vec↑ : Vec↑ _ (replicate Set₁)
test3Vec↑ = Set ◁̂ Set ◁̂ Set ◁̂ ε̂
\end{code}
