\begin{code}
module Category.Functor.Extra where

open import Function using (id)
open import Data.Unit using (⊤)
open import Category.Functor using (RawFunctor)
open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Category.Applicative.Indexed using (Morphism; module Morphism)
open RawApplicative using (rawFunctor)

open import Category.NaturalT using (NaturalT)
\end{code}


-- the identity functor
%<*IdF>
\AgdaTarget{IdF}
\begin{code}
IdF : ∀ {ℓ} → RawFunctor {ℓ} id
IdF = record { _<$>_ = id }
\end{code}
%</IdF>


-- transforms an applicative functor morphism into a regular natural transformation
%<*app-NaturalT>
\AgdaTarget{app-NaturalT}
\begin{code}
app-NaturalT : ∀ {ℓ} {F′ G′ : Set ℓ → Set ℓ}  {F : RawApplicative F′} {G : RawApplicative G′}
             → Morphism F G → NaturalT (rawFunctor F) (rawFunctor G)
app-NaturalT ηₐ = record { op = opₐ ηₐ; op-<$> = op-<$>ₐ ηₐ }
  where open Morphism using () renaming (op to opₐ; op-<$> to op-<$>ₐ)
\end{code}
%</app-NaturalT>


%<*product-functor>
\begin{code}
\end{code}
%</product-functor>
