\begin{code}
module NArySum where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true)
open import Data.Char using (Char)
open import Level using () renaming (suc to sucₗ)
open import Data.Vec using (Vec; lookup; replicate) renaming ([] to ε; _∷_ to _◁_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

\begin{code}
data Vec' {ℓ} : ∀ n (αₛ : Vec (Set ℓ) n) → Set (sucₗ ℓ) where
    ε   : Vec' 0 ε
    _◁_ : ∀ {α n αₛ} → α → Vec' n αₛ → Vec' (suc n) (α ◁ αₛ)

head' : ∀ {ℓ n α αₛ} → Vec' {ℓ} (suc n) (α ◁ αₛ) → α
head' (x ◁ xs) = x

lookup' : ∀ {ℓ n αₛ} (i : Fin n) → Vec' {ℓ} n αₛ → lookup i αₛ
lookup' Fz     (x ◁ xs) = x
lookup' (Fs j) (x ◁ xs) = lookup' j xs

ex1' : Vec' 3 (Bool ◁ ℕ ◁ Char ◁ ε)
ex1' = true ◁ 42 ◁ 'a' ◁ ε

Vec'-to-Vec : ∀ {ℓ α n} → Vec' {ℓ} n (replicate α) → Vec α n
Vec'-to-Vec ε        = ε
Vec'-to-Vec (x ◁ xs) = x ◁ Vec'-to-Vec xs

Vec-to-Vec' : ∀ {ℓ α n} → Vec α n → Vec' {ℓ} n (replicate α)
Vec-to-Vec' ε        = ε
Vec-to-Vec' (x ◁ xs) = x ◁ Vec-to-Vec' xs

ex2' : Vec' 5 (replicate ℕ)
ex2' = 40 ◁ 41 ◁ 42 ◁ 43 ◁ 44 ◁ ε

ex2 : Vec ℕ 5
ex2 = 40 ◁ 41 ◁ 42 ◁ 43 ◁ 44 ◁ ε

test : Vec'-to-Vec ex2' ≡ ex2
test = refl

inverse-right : ∀ {ℓ n} {α : Set ℓ} (v : Vec α n) → (Vec'-to-Vec ∘ Vec-to-Vec') v ≡ v
inverse-right ε                                 = refl
inverse-right (x ◁ xs) rewrite inverse-right xs = refl

inverse-left : ∀ {ℓ n} {α : Set ℓ} (v : Vec' n (replicate α)) → (Vec-to-Vec' ∘ Vec'-to-Vec) v ≡ v
inverse-left ε                                = refl
inverse-left (x ◁ xs) rewrite inverse-left xs = refl
\end{code}
