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


\begin{code}
infixr 30 _◁̂_

data Vec↑ {ℓ} : ∀ n → Vec (Set ℓ) n → Set (lsuc ℓ) where
    ε̂   : Vec↑ 0 ε
    _◁̂_ : ∀ {α : Set ℓ} {k} {αs} → α → Vec↑ k αs → Vec↑ (suc k) (α ◁ αs)
\end{code}

\begin{code}
infixr 30 _◁′_

data Vec↑I {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → Set ℓ₂) : ∀ n → Vec I n → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    ε′   : Vec↑I C 0 ε
    _◁′_ : ∀ {i k is} → C i → Vec↑I C k is → Vec↑I C (suc k) (i ◁ is)


infixr 30 _◁″_

data Vec↑A {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : I → I → Set ℓ₂) : ∀ n → Vec I n → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    [_]″ : ∀ {i₀ i₁} → C i₀ i₁ → Vec↑A C 1 [ i₀ ]
    _◁″_ : ∀ {i₀ i₁ k is} → C i₀ i₁ → Vec↑A C (suc k) (i₁ ◁ is) → Vec↑A C (suc (suc k)) (i₀ ◁ i₁ ◁ is)
\end{code}

\begin{code}
lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (i : Fin n) → Vec↑ n αs → lookup i αs
lookup↑ Fz      (x ◁̂ _)  = x
lookup↑ (Fs i′) (_ ◁̂ xs) = lookup↑ i′ xs
\end{code}


\begin{code}
head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (1 + n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x
\end{code}

\begin{code}
tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (1 + n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs
\end{code}

\begin{code}
[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂
\end{code}


\begin{code}
infixr 5 _++↑_

_++↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ++↑ ys = ys
(x ◁̂ xs) ++↑ ys = x ◁̂ (xs ++↑ ys)
\end{code}


\begin{code}
infixr 3 _⊛⇒_

_⊛⇒_ : ∀ {n ℓ} → Vec (Set ℓ) n → Vec (Set ℓ) n → Vec (Set ℓ) n
_⊛⇒_ = zipWith (λ α β → (α → β))
\end{code}

\begin{code}
infixr 4 _⊛↑_

_⊛↑_ : ∀ {n ℓ} {αs βs : Vec (Set ℓ) n} (fs : Vec↑ n (αs ⊛⇒ βs)) → Vec↑ n αs → Vec↑ n βs
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
