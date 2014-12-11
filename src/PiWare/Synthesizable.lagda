\begin{code}
open import PiWare.Atom

module PiWare.Synthesizable (At : Atomic) where

open import Function using (_∘_; _$_; const)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map⊎)
open import Data.Fin using (Fin; toℕ) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≟_; _⊔_)
open import Data.Vec using (Vec; _++_; splitAt; _>>=_; group; concat) renaming (_∷_ to _◁_; [] to ε; map to mapᵥ)
open import Data.List using (List) renaming (map to mapₗ)

import Algebra as A
import Data.Nat.Properties as NP
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (*-identity)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)
open import Relation.Nullary.Core using (yes; no)

open import PiWare.Padding using (padTo₁_withA_; unpadFrom₁; padTo₂_withA_; unpadFrom₂)
open import PiWare.Utils using (seggregateSums)
open Atomic At using (Atom; Atom#; atom→n; n→atom)
\end{code}


-- Words are sequences of "Atoms"
%<*Word>
\begin{code}
W : ℕ → Set
W = Vec Atom
\end{code}
%</Word>


-- Provides a mapping between "high-level" metalanguage types and words
%<*Synth>
\begin{code}
record ⇓W⇑ (α : Set) {i : ℕ} : Set where
    constructor ⇓W⇑[_,_]
    field
        ⇓ : α → W i
        ⇑ : W i → α
\end{code}
%</Synth>

\begin{code}
open ⇓W⇑ ⦃ ... ⦄
\end{code}


-- Sum-related tagging helpers
%<*untag>
\begin{code}
untag : ∀ {i j} → W (suc (i ⊔ j)) → W i ⊎ W j
untag {i} {j} (t ◁ ab) with toℕ (atom→n t) ≟ 1
untag {i} {j} (t ◁ ab) | yes _ = inj₂ (unpadFrom₂ i ab)
untag {i} {j} (t ◁ ab) | no  _ = inj₁ (unpadFrom₁ j ab)
\end{code}
%</untag>

%<*untagList>
\begin{code}
untagList : ∀ {i j} → List (W (suc (i ⊔ j))) → List (W i) × List (W j)
\end{code}
%</untagList-decl>
%<*untagList-def>
\begin{code}
untagList = seggregateSums ∘ mapₗ untag
\end{code}
%</untagList>


-- basic instances
\begin{code}
instance
\end{code}
%<*Synth-Unit>
\begin{code}
  ⇓W⇑-⊤ : ⇓W⇑ ⊤ {0}
  ⇓W⇑-⊤ = ⇓W⇑[ const ε , const tt ]
\end{code}
%</Synth-Unit>

%<*Synth-Product>
\begin{code}
instance
  ⇓W⇑-× : ∀ {α i β j} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α × β)
  ⇓W⇑-× {α} {i} {β} {j} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
      where down : (α × β) → W (i + j)
            down (a , b) = (⇓ {i = i} a) ++ (⇓ b)
  
            up : W (i + j) → (α × β)
            up w with splitAt i w
            up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = ⇑ ⇓a , ⇑ ⇓b
\end{code}
%</Synth-Product>

%<*Synth-Vec>
\begin{code}
instance
  ⇓W⇑-Vec : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ⇓W⇑ (Vec α n)
  ⇓W⇑-Vec {α} {i} {n} ⦃ sα ⦄ = ⇓W⇑[ down , up ]
      where group' : {α : Set} (n k : ℕ) → Vec α (n * k) → Vec (Vec α k) n
            group' n k = proj₁ ∘ group n k

            down : Vec α n → W (n * i)
            down = concat ∘ mapᵥ ⇓
            
            up : W (n * i) → Vec α n
            up = mapᵥ ⇑ ∘ group' n i
\end{code}
%</Synth-Vec>

%<*Synth-Sum>
\begin{code}
instance
  ⇓W⇑-⊎ : ∀ {α i β j} → (n m p : Atom#) {d : n ≢ m} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α ⊎ β) {suc (i ⊔ j)}
  ⇓W⇑-⊎ {α} {i} {β} {j} n m p ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
      where down : α ⊎ β → W (suc (i ⊔ j))
            down = [ (λ a → (n→atom n) ◁ (padTo₁ j withA n→atom p) (⇓ a))
                   , (λ b → (n→atom m) ◁ (padTo₂ i withA n→atom p) (⇓ b)) ]
            
            up : W (suc (i ⊔ j)) → α ⊎ β
            up = map⊎ (⇑ {i = i}) (⇑) ∘ untag
\end{code}
%</Synth-Sum>
