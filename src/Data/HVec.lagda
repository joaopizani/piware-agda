\begin{code}
module Data.HVec where

open import Level using (Lift) renaming (suc to lsuc)

open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool.Base using (true) renaming (Bool to B)
open import Data.Vec using (Vec; replicate; lookup; [_]; _++_) renaming ([] to ε; _∷_ to _◁_)
\end{code}


-- Type-heterogenenous vectors.
-- The "↑" in the name is pronounced "lifted", because these vectors are INDEXED by a vector of TYPES.
\begin{code}
infixr 30 _◁̂_

data Vec↑ {ℓ} : ∀ n → Vec (Set ℓ) n → Set (lsuc ℓ) where
    ε̂   : Vec↑ 0 ε
    _◁̂_ : ∀ {α : Set ℓ} {k} {αs} → α → Vec↑ k αs → Vec↑ (suc k) (α ◁ αs)
\end{code}


\begin{code}
lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (k : Fin n) → Vec↑ n αs → lookup k αs
lookup↑ Fz     (x ◁̂ _)  = x
lookup↑ (Fs k) (_ ◁̂ xs) = lookup↑ k xs
\end{code}


\begin{code}
head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x
\end{code}


\begin{code}
tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs
\end{code}


\begin{code}
[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂

vec↑ : ∀ {n ℓ} → Vec (Set ℓ) n → Set (lsuc ℓ)
vec↑ ε        = Lift ⊤
vec↑ (α ◁ αs) = α × vec↑ αs

lookup′↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (k : Fin n) → vec↑ αs → lookup k αs
lookup′↑ {αs = ε}      ()     _
lookup′↑ {αs = _ ◁ _} Fz     (x , _)  = x
lookup′↑ {αs = _ ◁ _} (Fs k) (_ , xs) = lookup′↑ k xs
\end{code}


\begin{code}
infixr 5 _⧺↑_

_⧺↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ⧺↑ ys = ys
(x ◁̂ xs) ⧺↑ ys = x ◁̂ (xs ⧺↑ ys)
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
\end{code}


\begin{code}
⊤s : ∀ {n} → Vec↑ n (replicate ⊤)
⊤s = replicate↑ tt
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
