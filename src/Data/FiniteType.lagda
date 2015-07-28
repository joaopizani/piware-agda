\begin{code}
module Data.FiniteType where

open import Level using (_⊔_)

open import Function using (_∘′_; flip)
open import Data.Nat.Base using (ℕ; zero; suc; _*_; _<″_)
open import Data.Nat.Properties.Simple using (*-right-zero)
open import Data.Fin using (Fin; toℕ; fromℕ≤″; _+_)
open import Data.Nat.DivMod using (module DivMod; _divMod_; _div_)
open import Data.Product using (_×_; _,_; map)
open import Data.Vec using (Vec; lookup)

open import Relation.Binary.PropositionalEquality using (refl)

open import Function.Bijection.Sets using (_LeftInverseOf′_)
open import Data.FiniteType.Base using (Finite; module Finite)
\end{code}


\begin{code}
open Finite ⦃ … ⦄
\end{code}


-- TODO
%<*splitFinLemma>
\AgdaTarget{splitFinLemma}
\begin{code}
postulate splitFinLemma : ∀ {x y} (i : Fin (x * suc y)) → (toℕ i) div (suc y) <″ x
\end{code}
%</splitFinLemma>


%<*splitFin×>
\AgdaTarget{splitFin×}
\begin{code}
splitFin× : ∀ {a b} → Fin (a * b) → Fin a × Fin b
splitFin× {a} {zero}    i  with (a * 0) | *-right-zero a
splitFin× {a} {zero}    () | .0         | refl
splitFin× {_} {suc b′}  i = fromℕ≤″ quotient (splitFinLemma i) , remainder
  where open DivMod ((toℕ i) divMod (suc b′)) 
\end{code}
%</splitFin×>


-- TODO
%<*joinFin×>
\AgdaTarget{joinFin×}
\begin{code}
postulate joinFin× : ∀ {a b} → Fin a × Fin b → Fin (a * b)
\end{code}
%</joinFin×>


%<*Finite-×>
\AgdaTarget{Finite-×}
\begin{code}
Finite-× : ∀ {ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} ⦃ fα : Finite {ℓ₁} α ⦄ ⦃ fβ : Finite {ℓ₂} β ⦄ → Finite {ℓ₁ ⊔ ℓ₂} (α × β)
Finite-× ⦃ fα ⦄ ⦃ fβ ⦄ = record { |α| = |α|′ * |β|′
                                ; surjection = record { to = to×; surjective = record { from = from×; right-inverse-of = to∘from× } } }
  where
    |α|′  = |α| ⦃ fα ⦄
    |β|′  = |α| ⦃ fβ ⦄
    to×   = map to to ∘′ splitFin×
    from× = joinFin× ∘′ map from from
\end{code}
%</Finite-×>
    -- TODO
\begin{code}
    postulate to∘from× : to× LeftInverseOf′ from×
\end{code}


\begin{code}
postulate _*′_ : ∀ {x} → Fin x → (y : ℕ) → Fin (x * y)
\end{code}

\begin{code}
postulate mapIx : ∀ {n ℓ₁ ℓ₂} {α : Set ℓ₁} {β : Set ℓ₂} → (Fin n → α → β) → Vec α n → Vec β n
\end{code}


\begin{code}
Finite-Vec : ∀ {n ℓ} {α : Set ℓ} ⦃ fα : Finite α ⦄ → Finite {ℓ} (Vec α n)
Finite-Vec {n} {_} {α} ⦃ fα ⦄ =  record { |α| = n * |α|′
                                        ; surjection = record { to = toVec; surjective = record { from = fromVec; right-inverse-of = to∘fromVec } } }
  where
    |α|′ = |α| ⦃ fα ⦄
    -- TODO
    postulate toVec : Fin (n * |α|′) → Vec α n
    postulate fromVec : Vec α n → Fin (n * |α|′) -- sumFin ∘′ mapIx (λ i a → (i *′ |α|′) + from a)
    postulate to∘fromVec : toVec LeftInverseOf′ fromVec
\end{code}
