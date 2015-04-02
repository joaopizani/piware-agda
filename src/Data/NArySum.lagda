\begin{code}
open import Level using () renaming (suc to lsuc)

open import Function using (_$_; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (true) renaming (Bool to B)
open import Data.Vec using (Vec; replicate; lookup; [_]; _++_; zipWith; _⊛_) renaming ([] to ε; _∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


data Vec↑ {ℓ} : ∀ n → Vec (Set ℓ) n → Set (lsuc ℓ) where
    ε̂   : Vec↑ 0 ε
    _◁̂_ : ∀ {α : Set ℓ} {k} {αs} → α → Vec↑ k αs → Vec↑ (suc k) (α ◁ αs)

infixr 30 _◁̂_

lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (i : Fin n) → Vec↑ n αs → lookup i αs
lookup↑ Fz      (x ◁̂ _)  = x
lookup↑ (Fs i′) (_ ◁̂ xs) = lookup↑ i′ xs


head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (1 + n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x

tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (1 + n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs

[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂


infixr 5 _++↑_

_++↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ++↑ ys = ys
(x ◁̂ xs) ++↑ ys = x ◁̂ (xs ++↑ ys)


infixr 3 _⊛⇒_

_⊛⇒_ : ∀ {n ℓ} → Vec (Set ℓ) n → Vec (Set ℓ) n → Vec (Set ℓ) n
_⊛⇒_ = zipWith (λ α β → (α → β))

infixr 4 _⊛↑_

_⊛↑_ : ∀ {n ℓ} {αs βs : Vec (Set ℓ) n} (fs : Vec↑ n (αs ⊛⇒ βs)) → Vec↑ n αs → Vec↑ n βs
_⊛↑_ {αs = ε}      {ε}      ε̂        ε̂        = ε̂
_⊛↑_ {αs = α ◁ αs} {β ◁ βs} (f ◁̂ fs) (x ◁̂ xs) = f x ◁̂ (fs ⊛↑ xs)


replicate↑ : ∀ {ℓ} {α : Set ℓ} {n} → α → Vec↑ n (replicate α)
replicate↑ {n = zero}   _ = ε̂
replicate↑ {n = suc n′} x = x ◁̂ replicate↑ x


--map↑ : ∀ {n ℓ} {α β : Set ℓ} → (α → β) → Vec↑ n (replicate α) → Vec↑ n (replicate β)
--map↑ f xs = replicate↑ f ⊛↑ xs



test1Vec↑ : Vec↑ _ (ℕ ◁ B ◁ ε)
test1Vec↑ = 3 ◁̂ true ◁̂ ε̂

test2Vec↑ : Vec↑ _ (replicate Set)
test2Vec↑ = ℕ ◁̂ B ◁̂ ℕ ◁̂ ε̂

test3Vec↑ : Vec↑ _ (replicate Set₁)
test3Vec↑ = Set ◁̂ Set ◁̂ Set ◁̂ ε̂


Vec↑-to-Vec : ∀ {n ℓ} {α : Set ℓ} → Vec↑ n (replicate α) → Vec α n
Vec↑-to-Vec ε̂        = ε
Vec↑-to-Vec (x ◁̂ xs) = x ◁ Vec↑-to-Vec xs

Vec-to-Vec↑ : ∀ {n ℓ} {α : Set ℓ} → Vec α n → Vec↑ n (replicate α)
Vec-to-Vec↑ ε        = ε̂
Vec-to-Vec↑ (x ◁ xs) = x ◁̂ Vec-to-Vec↑ xs

inverse-right : ∀ {n ℓ} {α : Set ℓ} (v : Vec α n) → (Vec↑-to-Vec ∘ Vec-to-Vec↑) v ≡ v
inverse-right ε                                 = refl
inverse-right (x ◁ xs) rewrite inverse-right xs = refl

inverse-left : ∀ {n ℓ} {α : Set ℓ} (v : Vec↑ n (replicate α)) → (Vec-to-Vec↑ ∘ Vec↑-to-Vec) v ≡ v
inverse-left ε̂                                = refl
inverse-left (x ◁̂ xs) rewrite inverse-left xs = refl
\end{code}
