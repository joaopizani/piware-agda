\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)

module PiWare.Synthesizable (At : Atomic) where

open import Function using (_∘′_; _$_; const)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; isInj₁; isInj₂; [_,_]) renaming (map to map⊎)
open import Data.Fin using () renaming (zero to Fz)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_)
open import Data.Vec using (Vec; _++_; splitAt; _>>=_; group; concat) renaming (_∷_ to _◁_; [] to ε; map to mapᵥ)
open import Data.List using (List; gfilter; map)

open import Data.Vec.Extra using (group')

open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PiWare.Padding using (padTo₁_withA_; unpadFrom₁; padTo₂_withA_; unpadFrom₂)
open Atomic At using (Atom; Atom#; W; atom→n; n→atom)
\end{code}


-- Provides a mapping between metalanguage types and words
%<*Synth>
\AgdaTarget{⇓W⇑, ⇓, ⇑}
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


-- Deduce Left or Right from tag. CONVENTION: Left = #0, Right by default (if atom→n t ≠ #0)
%<*untag>
\AgdaTarget{untag}
\begin{code}
untag : ∀ {i j} → W (suc (i ⊔ j)) → W i ⊎ W j
untag {i} {j} (t ◁ ab) = if ⌊ atom→n t ≟ Fz ⌋ then (inj₁ ∘′ unpadFrom₁ j) else (inj₂ ∘′ unpadFrom₂ i) $ ab
\end{code}
%</untag>

%<*seggregateSums>
\AgdaTarget{seggregateSums}
\begin{code}
seggregateSums : ∀ {ℓ} {α β : Set ℓ} → List (α ⊎ β) → List α × List β
seggregateSums = < gfilter isInj₁ , gfilter isInj₂ >
\end{code}
%</seggregateSums>

%<*untagList>
\AgdaTarget{untagList}
\begin{code}
untagList : ∀ {i j} → List (W (suc (i ⊔ j))) → List (W i) × List (W j)
untagList = seggregateSums ∘′ map untag
\end{code}
%</untagList>


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
instance
 ⇓W⇑-× : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α × β)
 ⇓W⇑-× {α} {i} {β} {j} ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
     where down : (α × β) → W (i + j)
           down (a , b) = (⇓ a) ++ (⇓ b)
 
           up : W (i + j) → (α × β)
           up w with splitAt i w
           up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = ⇑ ⇓a , ⇑ ⇓b
\end{code}
%</Synth-Product>


%<*Synth-Vec>
\AgdaTarget{⇓W⇑-Vec}
\begin{code}
instance
 ⇓W⇑-Vec : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ⇓W⇑ (Vec α n)
 ⇓W⇑-Vec {α} {i} {n} ⦃ sα ⦄ = ⇓W⇑[ down , up ]
   where
     down : Vec α n → W (n * i)
     down = concat ∘′ mapᵥ ⇓
           
     up : W (n * i) → Vec α n
     up = mapᵥ ⇑ ∘′ group' n i
\end{code}
%</Synth-Vec>


%<*Synth-Sum>
\AgdaTarget{⇓W⇑-⊎}
\begin{code}
instance
 ⇓W⇑-⊎ : ∀ {α i β j} (r p : Atom#) {d : r ≢ Fz} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ⇓W⇑ (α ⊎ β) {suc (i ⊔ j)}
 ⇓W⇑-⊎ {α} {i} {β} {j} r p ⦃ sα ⦄ ⦃ sβ ⦄ = ⇓W⇑[ down , up ]
   where down : α ⊎ β → W (suc (i ⊔ j))
         down = [ (λ a → (n→atom Fz) ◁ (padTo₁ j withA n→atom p) (⇓ a))
                , (λ b → (n→atom r)  ◁ (padTo₂ i withA n→atom p) (⇓ b)) ]
           
         up : W (suc (i ⊔ j)) → α ⊎ β
         up = map⊎ ⇑ ⇑ ∘′ untag
\end{code}
%</Synth-Sum>
