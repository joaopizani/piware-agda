\begin{code}
open import Level using () renaming (suc to lsuc)

open import Function using (_$_; _∘_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool.Base using (true) renaming (Bool to B)
open import Data.Vec using (Vec; replicate; lookup; [_]; _++_; zipWith; _⊛_) renaming ([] to ε; _∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}


%<*Vec-hetero>
\AgdaTarget{Vec↑, ε̂, \_◁̂\_}
\begin{code}
infixr 30 _◁̂_

data Vec↑ {ℓ} : ∀ n → Vec (Set ℓ) n → Set (lsuc ℓ) where
    ε̂   : Vec↑ 0 ε
    _◁̂_ : ∀ {α : Set ℓ} {k} {αs} → α → Vec↑ k αs → Vec↑ (suc k) (α ◁ αs)
\end{code}
%</Vec-hetero>


%<*lookup-hetero>
\AgdaTarget{lookup↑}
\begin{code}
lookup↑ : ∀ {n ℓ} {αs : Vec (Set ℓ) n} (i : Fin n) → Vec↑ n αs → lookup i αs
lookup↑ Fz      (x ◁̂ _)  = x
lookup↑ (Fs i′) (_ ◁̂ xs) = lookup↑ i′ xs
\end{code}
%</lookup-hetero>


%<*head-hetero>
\AgdaTarget{head↑}
\begin{code}
head↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → α
head↑ (x ◁̂ _) = x
\end{code}
%</head-hetero>


%<*tail-hetero>
\AgdaTarget{tail↑}
\begin{code}
tail↑ : ∀ {n ℓ} {α : Set ℓ} {αs : Vec (Set ℓ) n} → Vec↑ (suc n) (α ◁ αs) → Vec↑ n αs
tail↑ (_ ◁̂ xs) = xs
\end{code}
%</tail-hetero>


%<*singleton-hetero>
\AgdaTarget{[\_]↑}
\begin{code}
[_]↑ : ∀ {ℓ} {α : Set ℓ} → α → Vec↑ 1 [ α ]
[ x ]↑ = x ◁̂ ε̂
\end{code}
%</singleton-hetero>


%<*append-hetero>
\AgdaTarget{\_++\_}
\begin{code}
infixr 5 _++↑_

_++↑_ : ∀ {m n ℓ} {αs : Vec (Set ℓ) m} {βs : Vec (Set ℓ) n} → Vec↑ m αs → Vec↑ n βs → Vec↑ (m + n) (αs ++ βs)
ε̂        ++↑ ys = ys
(x ◁̂ xs) ++↑ ys = x ◁̂ (xs ++↑ ys)
\end{code}
%</append-hetero>


%<*zipWith-arrow>
\AgdaTarget{\_⊛⇒\_}
\begin{code}
infixr 3 _⊛⇒_

_⊛⇒_ : ∀ {n ℓ} → Vec (Set ℓ) n → Vec (Set ℓ) n → Vec (Set ℓ) n
_⊛⇒_ = zipWith (λ α β → (α → β))
\end{code}
%</zipWith-arrow>

%<*fapply-hetero>
\AgdaTarget{\_⊛↑\_}
\begin{code}
infixr 4 _⊛↑_

_⊛↑_ : ∀ {n ℓ} {αs βs : Vec (Set ℓ) n} (fs : Vec↑ n (αs ⊛⇒ βs)) → Vec↑ n αs → Vec↑ n βs
_⊛↑_ {αs = ε}      {ε}      ε̂        ε̂        = ε̂
_⊛↑_ {αs = α ◁ αs} {β ◁ βs} (f ◁̂ fs) (x ◁̂ xs) = f x ◁̂ (fs ⊛↑ xs)
\end{code}
%</fapply-hetero>


%<*replicate-hetero>
\AgdaTarget{replicate↑}
\begin{code}
replicate↑ : ∀ {ℓ} {α : Set ℓ} {n} → α → Vec↑ n (replicate α)
replicate↑ {n = zero}   _ = ε̂
replicate↑ {n = suc n′} x = x ◁̂ replicate↑ x
\end{code}
%</replicate-hetero>


%<*map-hetero>
\AgdaTarget{map↑}
\begin{code}
--map↑ : ∀ {n ℓ} {α β : Set ℓ} → (α → β) → Vec↑ n (replicate α) → Vec↑ n (replicate β)
--map↑ f xs = replicate↑ f ⊛↑ xs
\end{code}
%</map-hetero>


%<hetero-to-homo>
\AgdaTarget{Vec↑-to-Vec}
\begin{code}
Vec↑-to-Vec : ∀ {n ℓ} {α : Set ℓ} → Vec↑ n (replicate α) → Vec α n
Vec↑-to-Vec ε̂        = ε
Vec↑-to-Vec (x ◁̂ xs) = x ◁ Vec↑-to-Vec xs
\end{code}
%</hetero-to-homo>

%<*homo-to-hetero>
\AgdaTarget{Vec-to-Vec↑}
\begin{code}
Vec-to-Vec↑ : ∀ {n ℓ} {α : Set ℓ} → Vec α n → Vec↑ n (replicate α)
Vec-to-Vec↑ ε        = ε̂
Vec-to-Vec↑ (x ◁ xs) = x ◁̂ Vec-to-Vec↑ xs
\end{code}
%</homo-to-hetero>

%<*inverse-right>
\AgdaTarget{inverse-right}
\begin{code}
inverse-right : ∀ {n ℓ} {α : Set ℓ} (v : Vec α n) → (Vec↑-to-Vec ∘ Vec-to-Vec↑) v ≡ v
inverse-right ε                                 = refl
inverse-right (x ◁ xs) rewrite inverse-right xs = refl
\end{code}
%<*inverse-right>

%</inverse-left>
\AgdaTarget{inverse-left}
\begin{code}
inverse-left : ∀ {n ℓ} {α : Set ℓ} (v : Vec↑ n (replicate α)) → (Vec-to-Vec↑ ∘ Vec↑-to-Vec) v ≡ v
inverse-left ε̂                                = refl
inverse-left (x ◁̂ xs) rewrite inverse-left xs = refl
\end{code}
%<*inverse-left>


%<*test1>
\AgdaTarget{test1Vec↑}
\begin{code}
test1Vec↑ : Vec↑ _ (ℕ ◁ B ◁ ε)
test1Vec↑ = 3 ◁̂ true ◁̂ ε̂
\end{code}
%</test1>

%<*test2>
\AgdaTarget{test2Vec↑}
\begin{code}
test2Vec↑ : Vec↑ _ (replicate Set)
test2Vec↑ = ℕ ◁̂ B ◁̂ ℕ ◁̂ ε̂
\end{code}
%</test2>

%<*test3>
\AgdaTarget{test3Vec↑}
\begin{code}
test3Vec↑ : Vec↑ _ (replicate Set₁)
test3Vec↑ = Set ◁̂ Set ◁̂ Set ◁̂ ε̂
\end{code}
%</test3>
