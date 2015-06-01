\begin{code}
module Data.Vec.Extra where

open import Function using (id; _∘_)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_)
open import Data.Product using (∃₂; _×_; proj₁; proj₂; map)
open import Data.Vec using (Vec; splitAt; _++_; group; initLast; applicative)

open import Category.Functor using (RawFunctor)
open import Category.Applicative.Indexed using (module RawIApplicative)
open RawIApplicative using (rawFunctor)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Category.NaturalT using (NaturalT)
\end{code}


%<*proj-synonyms>
\AgdaTarget{₁,₂}
\begin{code}
₁ = proj₁
₂ = proj₂
\end{code}
%</proj-synonyms>

%<*proj₂-ignore-eq>
\AgdaTarget{proj₂′}
\begin{code}
proj₂′ : ∀ {n m ℓ} {α : Set ℓ} {xs : Vec α (n + m)} → (∃₂ λ (ys : Vec α n) (zs : Vec α m) → xs ≡ ys ++ zs) → Vec α m
proj₂′ = proj₁ ∘ proj₂
\end{code}
%</proj₂-ignore-eq>

%<*p₂-ignore-eq>
\AgdaTarget{₂′}
\begin{code}
₂′ : ∀ {n m ℓ} {α : Set ℓ} {xs : Vec α (n + m)} → (∃₂ λ (ys : Vec α n) (zs : Vec α m) → xs ≡ ys ++ zs) → Vec α m
₂′ = proj₂′
\end{code}
%</p₂-ignore-eq>


%<*splitAt-noproof>
\AgdaTarget{splitAt′}
\begin{code}
splitAt′ : ∀ {ℓ} {α : Set ℓ} m {n} → Vec α (m + n) → Vec α m × Vec α n
splitAt′ m v = map id proj₁ (splitAt m v)
\end{code}
%</splitAt-noproof>


%<*group-ignore-eq>
\AgdaTarget{group′}
\begin{code}
group′ : ∀ {ℓ} {α : Set ℓ} n k → Vec α (n * k) → Vec (Vec α k) n
group′ n k = proj₁ ∘ group n k
\end{code}
%</group-ignore-eq>


%<*initLast-noproof>
\AgdaTarget{initLast′}
\begin{code}
initLast′ : ∀ {ℓ n} {α : Set ℓ} (xs : Vec α (suc n)) → Vec α n × α
initLast′ = map id proj₁ ∘ initLast
\end{code}
%</initLast-noproof>


%<*VecF>
\AgdaTarget{VecF}
\begin{code}
VecF : ∀ {ℓ} n → RawFunctor (λ (α : Set ℓ) → Vec α n)
VecF n = rawFunctor applicative
\end{code}
%</VecF>


%<*VecNaturalT>
\AgdaTarget{VecNaturalT}
\begin{code}
VecNaturalT : ∀ {ℓ} → ℕ → ℕ → Set _
VecNaturalT {ℓ} m n = NaturalT (VecF {ℓ} m) (VecF {ℓ} n)
\end{code}
%</VecNaturalT>
