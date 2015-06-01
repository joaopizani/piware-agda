\begin{code}
module Category.NaturalT where

open import Level using (Level) renaming (suc to lsuc)

open import Function using (_∘_)
open import Category.Functor using (RawFunctor; module RawFunctor)
open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


-- natural transformations
%<*NaturalT>
\AgdaTarget{NaturalT}
\begin{code}
record NaturalT {ℓ} {F′ G′ : Set ℓ → Set ℓ} (F : RawFunctor F′) (G : RawFunctor G′) : Set (lsuc ℓ) where
  open module F = RawFunctor F using () renaming (_<$>_ to _<$ᶠ>_)
  open module G = RawFunctor G using () renaming (_<$>_ to _<$ᵍ>_)
  field
    op      : ∀ {X} → F′ X → G′ X
    op-<$>  : ∀ {X Y} (f : X → Y) x → op (f <$ᶠ> x) ≡ (f <$ᵍ> (op x))
\end{code}
%</NaturalT>


-- vertical composition (component-wise)
%<*NaturalT-composition-vertical>
\AgdaTarget{\_∘⇓\_}
\begin{code}
_∘⇓_ : ∀ {ℓ} {F′ G′ H′ : Set ℓ → Set ℓ} {F : RawFunctor F′} {G : RawFunctor G′} {H : RawFunctor H′}
       → NaturalT G H → NaturalT F G → NaturalT F H
_∘⇓_ {F = F} {_} {H} ε η = record { op = op ε ∘ op η;  op-<$> = ∘-<$> }
  where
    open module F = RawFunctor F using () renaming (_<$>_ to _<$ᶠ>_)
    open module H = RawFunctor H using () renaming (_<$>_ to _<$ʰ>_)
    open NaturalT using (op; op-<$>)

    -- the (vertical) composition of natural transformations is a natural transformation
    ∘-<$> : ∀ {X Y} (f : X → Y) x → (op ε ∘ op η) (f <$ᶠ> x) ≡ (f <$ʰ> ((op ε ∘ op η) x))
    ∘-<$> f x rewrite op-<$> η f x = op-<$> ε f (op η x)
\end{code}
%</NaturalT-composition-vertical>
