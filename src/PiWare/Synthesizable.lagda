\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)

module PiWare.Synthesizable (At : Atomic) where

open import Function using (_∘′_; const)
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (suc; _+_; _*_; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map⊎)
open import Data.Fin using () renaming (zero to Fz)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec; _++_; splitAt; concat) renaming (_∷_ to _◁_; [] to ε; map to mapᵥ)

open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Vec.Extra using (group′)
open import Function.Bijection.Sets using (module Inverse′)
open Inverse′ using (from; to)

open import PiWare.Padding using (padTo₁_withA_; unpadFrom₁; padTo₂_withA_; unpadFrom₂)
open import PiWare.Interface using (Ix)
open Atomic At using (Atom#; W; enum)
\end{code}


-- Provides a mapping between metalanguage types and sets of words
%<*Synth>
\AgdaTarget{⇓W⇑, ⇓, ⇑}
\begin{code}
record ⇓W⇑ (α : Set) {i : Ix} : Set where
    constructor ⇓W⇑[_,_]
    field ⇓ : α → W i
          ⇑ : W i → α
\end{code}
%</Synth>

\begin{code}
open ⇓W⇑ ⦃ ... ⦄
\end{code}


-- basic instances
\begin{code}
instance
\end{code}

%<*Synth-Unit>
\AgdaTarget{⇓W⇑-⊤}
\begin{code}
 ⇓W⇑-⊤ : ⇓W⇑ ⊤ {0}
 ⇓W⇑-⊤ = ⇓W⇑[ const ε , const tt ]
\end{code}
%</Synth-Unit>

%<*Synth-Product>
\AgdaTarget{⇓W⇑-×}
\begin{code}
 ⇓W⇑-× : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α × β)
 ⇓W⇑-× {α} {i} {β} {j} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
   where
     down : (α × β) → W (i + j)
     down (a , b) = (⇓ {i = i} a) ++ (⇓ b)
 
     up : W (i + j) → (α × β)
     up w with splitAt i w
     up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = ⇑ ⇓a , ⇑ ⇓b
\end{code}
%</Synth-Product>

%<*Synth-Vec>
\AgdaTarget{⇓W⇑-Vec}
\begin{code}
 ⇓W⇑-Vec : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ⇓W⇑ (Vec α n)
 ⇓W⇑-Vec {α} {i} {n} ⦃ sα ⦄ = ⇓W⇑[ down , up ]
   where
     down : Vec α n → W (n * i)
     down = concat ∘′ mapᵥ ⇓
           
     up : W (n * i) → Vec α n
     up = mapᵥ ⇑ ∘′ group′ n i
\end{code}
%</Synth-Vec>


-- Deduce Left or Right from tag. TODO CONVENTION: Left = #0, Right by default (if atom→n t ≠ #0)
%<*untag>
\AgdaTarget{untag}
\begin{code}
untag : ∀ {i j} → W (suc (i ⊔ j)) → W i ⊎ W j
untag {i} {j} (t ◁ ab) = ( if ⌊ from enum t ≟ Fz ⌋
                           then (inj₁ ∘′ unpadFrom₁ j)
                           else (inj₂ ∘′ unpadFrom₂ i)
                         ) ab
\end{code}
%</untag>

\begin{code}
instance
\end{code}
%<*Synth-Sum>
\AgdaTarget{⇓W⇑-⊎}
\begin{code}
 ⇓W⇑-⊎ : ∀ {α i β j} (r p : Atom#) {d : r ≢ Fz} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α ⊎ β) {suc (i ⊔ j)}
 ⇓W⇑-⊎ {α} {i} {β} {j} r p ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
   where
     down : α ⊎ β → W (suc (i ⊔ j))
     down = [ (λ a → (to enum Fz) ◁ (padTo₁ j withA (to enum p)) (⇓ {i = i} a))
            , (λ b → (to enum r)  ◁ (padTo₂ i withA (to enum p)) (⇓ b)) ]
       
     up : W (suc (i ⊔ j)) → α ⊎ β
     up = map⊎ (⇑ {i = i}) (⇑ {i = j}) ∘′ untag
\end{code}
%</Synth-Sum>
