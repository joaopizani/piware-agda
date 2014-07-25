\begin{code}
module Report.ChapterIntroduction where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Vec using (Vec; _∷_; []; concat; _++_; splitAt)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


%<*Vect-head>
\begin{code}
data Vect (α : Set) : ℕ → Set where
    ε    : Vect α zero
    _∷_  : ∀ {n} → α → Vect α n → Vect α (suc n)

head : ∀ {α n} → Vect α (suc n) → α
head (x ∷ xs) = x
\end{code}
%</Vect-head>


%<*group-decl>
\begin{code}
group : ∀ {α : Set} n k  → (xs : Vec α (n * k))
                         → ∃ λ (xss : Vec (Vec α k) n) → xs ≡ concat xss
\end{code}
%</group-decl>
%<*group-def>
\begin{code}
group zero k [] = ([] , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) = ((ys ∷ zss) , refl)
\end{code}
%</group-def>
