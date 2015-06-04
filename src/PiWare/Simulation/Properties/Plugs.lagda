\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties.Plugs {At : Atomic} (Gt : Gates At) where

open import Function using (flip; _$_; _∘_; id; _⟨_⟩_)
open import Data.Vec using (Vec; lookup; tabulate; allFin; map)
open import Data.Vec.Properties using (lookup-morphism; tabulate∘lookup; lookup∘tabulate; map-lookup-allFin)
open import Data.Vec.Equality using (module PropositionalEquality)
open PropositionalEquality using (from-≡)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; cong; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_; _≡⟨⟩_)

open import Category.Functor.Extra using (app-NaturalT)
open import Category.NaturalT using (module NaturalT; _∘⇓_)
open NaturalT using (op; op-<$>)
open import Data.Vec.Extra using (VecNaturalT)
open import Data.Vec.Properties.Extra using (tabulate-ext)

open import PiWare.Circuit using (_⟫_)
open import PiWare.Plugs Gt using (plug-Vecη; id⤨)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWare.Simulation.Equality Gt using (_≅_; _≋_; ≅⇒≋; ≋-refl; ≋-trans)
open Atomic At using (W)
\end{code}


%<*flip-lookup>
\AgdaTarget{lookupᵗ}
\begin{code}
lookupᵗ : ∀ {ℓ n} {α : Set ℓ} → Vec α n → Fin n → α
lookupᵗ = flip lookup
\end{code}
%</flip-lookup>


%<*plug-Vec-eta-sim>
\AgdaTarget{plug-Vecη-⟦⟧}
\begin{code}
plug-Vecη-⟦⟧ : ∀ {i o} (η : VecNaturalT i o) (w : W i) → ⟦ plug-Vecη η ⟧ w ≡ op η w
plug-Vecη-⟦⟧ {i} η w = begin
    tabulate (λ i → lookupᵗ w (lookup i $ op η (allFin _))) ≡⟨ tabulate-ext (λ i → sym $ op-<$> (app-NaturalT $ lookup-morphism i) (lookupᵗ w) _) ⟩
    tabulate (lookupᵗ (map (lookupᵗ w) (op η (allFin _))))  ≡⟨ tabulate-ext (λ i → sym $ cong (lookup i) (op-<$> η (lookupᵗ w) _)) ⟩
    tabulate (lookupᵗ (op η (map (lookupᵗ w) (allFin _))))  ≡⟨ tabulate∘lookup _ ⟩
    op η (map (lookupᵗ w) (allFin _))                       ≡⟨ cong (op η) (map-lookup-allFin _) ⟩
    op η w
  ∎
\end{code}
%</plug-Vec-eta-sim>


%<*id-plug-implements-id>
\AgdaTarget{id⤨-id}
\begin{code}
id⤨-id : ∀ {i} (w : W i) → ⟦ id⤨ ⟧ w ≡ id w
id⤨-id w = begin
    ⟦ id⤨ ⟧ w                                  ≡⟨⟩  -- by definition of ⟦_⟧
    tabulate (lookupᵗ w ∘ lookupᵗ (allFin _))  ≡⟨ tabulate-ext (cong (lookupᵗ w) ∘ lookup∘tabulate id) ⟩
    tabulate (lookupᵗ w)                       ≡⟨ tabulate∘lookup w ⟩
    id w
  ∎
\end{code}
%</id-plug-implements-id>


%<*id⤨-cong>
\begin{code}
id⤨-cong : ∀ {i j} (p : i ≡ j) → id⤨ {i} ≋ id⤨ {j}
id⤨-cong refl = ≋-refl
\end{code}
%</id⤨-cong>


\begin{code}
private
\end{code}
%<*plug-Vec-eta-id-one-input>
\AgdaTarget{plug-Vecη-id′}
\begin{code}
 plug-Vecη-id′ : ∀ {j} (η : VecNaturalT j j) → (∀ {X} (w : Vec X j) → op η w ≡ w) → plug-Vecη η ≅ id⤨
 plug-Vecη-id′ η η-id w = from-≡ $ begin
     ⟦ plug-Vecη η ⟧ w  ≡⟨ plug-Vecη-⟦⟧ η w ⟩
     op η w             ≡⟨ η-id w ⟩
     w                  ≡⟨ sym (id⤨-id w) ⟩
     ⟦ id⤨ ⟧ w
   ∎
\end{code}
%</plug-Vec-eta-id-one-input>


\begin{code}
private
\end{code}
%<*plug-Vec-eta-comp-one-input>
\AgdaTarget{plug-Vecη-∘′}
\begin{code}
 plug-Vecη-∘′ : ∀ {i m o} (η : VecNaturalT i m) (ε : VecNaturalT m o) → plug-Vecη η ⟫ plug-Vecη ε ≅ plug-Vecη (ε ∘⇓ η)
 plug-Vecη-∘′ η ε w = from-≡ $
   begin
     ⟦ plug-Vecη η ⟫ plug-Vecη ε ⟧ w       ≡⟨⟩
     ⟦ plug-Vecη ε ⟧ (⟦ plug-Vecη η ⟧ w)   ≡⟨ plug-Vecη-⟦⟧ ε (⟦ plug-Vecη η ⟧ w) ⟩
     op ε (⟦ plug-Vecη η ⟧ w)              ≡⟨ cong (op ε) (plug-Vecη-⟦⟧ η w) ⟩
     (op ε ∘ op η) w                       ≡⟨⟩
     op (ε ∘⇓ η) w                         ≡⟨ sym (plug-Vecη-⟦⟧ (ε ∘⇓ η) w) ⟩
     ⟦ plug-Vecη (ε ∘⇓ η) ⟧ w
   ∎
\end{code}
%</plug-Vec-eta-comp-one-input>


\begin{code}
private
\end{code}
%<*plug-Vec-eta-ext-one-input>
\AgdaTarget{plug-Vecη-ext′}
\begin{code}
 plug-Vecη-ext′ : ∀ {i o} (η : VecNaturalT i o) (ε : VecNaturalT i o)
                  → (∀ {X} (w : Vec X i) → op η w ≡ op ε w) → plug-Vecη η ≅ plug-Vecη ε
 plug-Vecη-ext′ η ε η≈ε w = from-≡ $ begin
     ⟦ plug-Vecη η ⟧ w  ≡⟨ plug-Vecη-⟦⟧ η w ⟩
     op η w             ≡⟨ η≈ε w ⟩
     op ε w             ≡⟨ sym (plug-Vecη-⟦⟧ ε w) ⟩
     ⟦ plug-Vecη ε ⟧ w
   ∎
\end{code}
%</plug-Vec-eta-ext-one-input>


%<*plug-Vec-eta-id>
\AgdaTarget{plug-Vecη-id}
\begin{code}
plug-Vecη-id : ∀ {j} (η : VecNaturalT j j) → (∀ {X : Set} (w : Vec X j) → op η w ≡ w) → plug-Vecη η ≋ id⤨
plug-Vecη-id η p = ≅⇒≋ (plug-Vecη-id′ η p)
\end{code}
%</plug-Vec-eta-id>


%<*plug-Vec-eta-comp>
\AgdaTarget{plug-Vecη-∘}
\begin{code}
plug-Vecη-∘ : ∀ {i m o} (η : VecNaturalT i m) (ε : VecNaturalT m o) → plug-Vecη η ⟫ plug-Vecη ε ≋ plug-Vecη (ε ∘⇓ η)
plug-Vecη-∘ η ε = ≅⇒≋ (plug-Vecη-∘′ η ε)
\end{code}
%</plug-Vec-eta-comp>


%<*plug-Vec-eta-ext>
\AgdaTarget{plug-Vecη-ext}
\begin{code}
plug-Vecη-ext : ∀ {i o} {η : VecNaturalT i o} {ε : VecNaturalT i o}
                → (∀ {X} (w : Vec X i) → op η w ≡ op ε w) → plug-Vecη η ≋ plug-Vecη ε
plug-Vecη-ext {η = η} {ε} p = ≅⇒≋ (plug-Vecη-ext′ η ε p)
\end{code}
%</plug-Vec-eta-ext>


%<*plugs-Vec-eta-inverse>
\AgdaTarget{plugs-Vecη⁻¹}
\begin{code}
plugs-Vecη⁻¹ : ∀ {i o} (η : VecNaturalT i o) (ε : VecNaturalT o i)
               → (∀ {X} (w : Vec X i) → (op ε ∘ op η) w ≡ w) → plug-Vecη η ⟫ plug-Vecη ε ≋ id⤨ {i}
plugs-Vecη⁻¹ η ε p = plug-Vecη-∘ η ε ⟨ ≋-trans ⟩ plug-Vecη-id (ε ∘⇓ η) p
\end{code}
%</plugs-Vec-eta-inverse>
