\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _∘′_; _$_; flip; _⟨_⟩_)
open import Data.Nat.Base using (_+_)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; lookup; tabulate; splitAt; allFin; map)

open import Relation.Binary.Indexed.Core using (module Setoid)
open import Data.Nat.Properties.Simple using (+-right-identity; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; setoid; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_; _≡⟨⟩_)

open import Data.Vec.Equality using () renaming (module PropositionalEquality to VecPropEq)
open VecPropEq using (from-≡; to-≡; _≈_) renaming (refl to reflᵥ)
open import Data.Vec.Properties using (tabulate-allFin; tabulate∘lookup; lookup∘tabulate; lookup-morphism; map-lookup-allFin)
open module X {a} {α : Set a} = Data.Vec.Properties.UsingVectorEquality (setoid α) using (xs++[]=xs)

open import Data.Vec.Extra using (₁; ₂′; VecNaturalT)
open import Data.Vec.Properties.Extra
  using (proj₁∘splitAt-last≈; ++-assoc; ++-assoc-split₁; ++-assoc-split₂; ++-assoc-split₃; splitAt-++; tabulate-ext)

open import Category.NaturalT using (module NaturalT; _∘⇓_)
open import Category.Functor.Extra using (app-NaturalT)
open NaturalT using (op; op-<$>)

open Atomic At using (W)
open import PiWare.Plugs Gt using (id⤨; plug-Vecη)
open import PiWare.Circuit using (ℂ; _⟫_; _∥_)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWare.Simulation.Equality Gt using (_≅_; _≋_; refl≋; ≅⇒≋; ≋-setoid)
open Setoid ≋-setoid using () renaming (sym to ≋-sym; refl to ≋-refl; trans to ≋-trans)
\end{code}


%<*flip-lookup>
\AgdaTarget{lookupᵗ}
\begin{code}
lookupᵗ : ∀ {ℓ n} {α : Set ℓ} → Vec α n → Fin n → α
lookupᵗ = flip lookup
\end{code}
%</flip-lookup>


-- TODO: Could be made to hold by definition
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
    ⟦ id⤨ ⟧ w                                   ≡⟨⟩  -- by definition of ⟦_⟧
    tabulate (lookupᵗ w ∘′ lookupᵗ (allFin _))  ≡⟨ tabulate-ext (cong (lookupᵗ w) ∘ lookup∘tabulate id) ⟩
    tabulate (lookupᵗ w)                        ≡⟨ tabulate∘lookup w ⟩
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



%<*seq-right-identity>
\AgdaTarget{⟫-right-identity}
\begin{code}
⟫-right-identity : ∀ {i o} (c : ℂ i o) → c ⟫ id⤨ ≋ c
⟫-right-identity c = ≅⇒≋ (from-≡ ∘ id⤨-id ∘ ⟦ c ⟧)
\end{code}
%</seq-right-identity>

%<*seq-left-identity>
\AgdaTarget{⟫-left-identity}
\begin{code}
⟫-left-identity : ∀ {i o} (c : ℂ i o) → id⤨ ⟫ c ≋ c
⟫-left-identity c = ≅⇒≋ (from-≡ ∘ cong ⟦ c ⟧ ∘ id⤨-id)
\end{code}
%</seq-left-identity>

%<*seq-assoc>
\AgdaTarget{⟫-assoc}
\begin{code}
⟫-assoc : ∀ {i m n o} (c₁ : ℂ i m) (c₂ : ℂ m n) (c₃ : ℂ n o) → (c₁ ⟫ c₂) ⟫ c₃ ≋ c₁ ⟫ (c₂ ⟫ c₃)
⟫-assoc c₁ c₂ c₃ = ≅⇒≋ (from-≡ ∘ λ _ → refl)
\end{code}
%</seq-assoc>


%<*par-left-identity>
\AgdaTarget{∥-left-identity}
\begin{code}
∥-left-identity : ∀ {i o} (c : ℂ i o) → id⤨ {0} ∥ c ≋ c
∥-left-identity _ = ≅⇒≋ (λ _ → reflᵥ _)
\end{code}
%</par-left-identity>

%<*par-right-identity>
\AgdaTarget{∥-right-identity}
\begin{code}
∥-right-identity : ∀ {i o} (c : ℂ i o) → c ∥ id⤨ {0} ≋ c
∥-right-identity {i} {o} c = refl≋ (+-right-identity i) ∥-right-identity′
  where ∥-right-identity′ : ∀ {w w′} → w ≈ w′ → ⟦ c ∥ id⤨ {0} ⟧ w ≈ ⟦ c ⟧ w′
        ∥-right-identity′ w≈w′ rewrite to-≡ (proj₁∘splitAt-last≈ w≈w′) = xs++[]=xs (⟦ c ⟧ _)
\end{code}
%</par-right-identity>

%<*par-assoc>
\AgdaTarget{∥-assoc}
\begin{code}
∥-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} {c₃ : ℂ i₃ o₃} → (c₁ ∥ c₂) ∥ c₃ ≋ c₁ ∥ (c₂ ∥ c₃)
∥-assoc {i₁} {_} {i₂} {_} {i₃} {_} {c₁} {c₂} {c₃} = refl≋ (+-assoc i₁ i₂ i₃) ∥-assoc-≊  
  where ∥-assoc-≊ : ∀ {w w′} → w ≈ w′ → ⟦ (c₁ ∥ c₂) ∥ c₃ ⟧ w ≈ ⟦ c₁ ∥ (c₂ ∥ c₃) ⟧ w′
        ∥-assoc-≊ {w} {w′} w≈w′ rewrite to-≡ $ ++-assoc-split₁ {i₁} w≈w′
                                      | to-≡ $ ++-assoc-split₂ {i₁} w≈w′
                                      | sym (to-≡ $ ++-assoc-split₃ {i₁} w≈w′)
          = ++-assoc (⟦ c₁ ⟧ w₁) (⟦ c₂ ⟧ w₂) (⟦ c₃ ⟧ w₃)
          where w₁ = ₁ (splitAt i₁ w′)
                w₂ = (₁ ∘ splitAt i₂ ∘ ₂′) (splitAt i₁ w′)
                w₃ = ₂′ (splitAt (i₁ + i₂) w)
\end{code}
%</par-assoc>


-- Fusion law of identity plugs
%<*id-plug-par-fusion>
\AgdaTarget{∥-id⤨}
\begin{code}
∥-id⤨ : ∀ {n m} → id⤨ {n} ∥ id⤨ {m} ≋ id⤨ {n + m}
∥-id⤨ {n} {m} = ≅⇒≋ (from-≡ ∘ f)
  where f : ∀ w → ⟦ id⤨ {n} ∥ id⤨ {m} ⟧ w ≡ ⟦ id⤨ {n + m} ⟧ w
        f w with splitAt n w
        f w | wₙ , wₘ , w≡wₙ⧺wₘ with id⤨-id wₙ | id⤨-id wₘ | id⤨-id w
        f w | wₙ , wₘ , w≡wₙ⧺wₘ | eq-wₙ | eq-wₘ | eq-w rewrite eq-wₙ | eq-wₘ | eq-w = sym w≡wₙ⧺wₘ
\end{code}
%</id-plug-par-fusion>


-- Circuits in "row-major order" to "column-major order"
%<*rows-to-cols>
\AgdaTarget{rows-to-cols}
\begin{code}
rows-to-cols : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ i₁ m₁) (f₂ : ℂ i₂ m₂) (g₁ : ℂ m₁ o₁) (g₂ : ℂ m₂ o₂)
               → (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂) ≋ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂)
rows-to-cols {i₁} {m₁} f₁ f₂ g₁ g₂ = ≅⇒≋ (from-≡ ∘ f)
  where f : ∀ w → ⟦ (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂) ⟧ w ≡ ⟦ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂) ⟧ w
        f w rewrite splitAt-++ m₁ (⟦ f₁ ⟧ $ ₁ (splitAt i₁ w)) (⟦ f₂ ⟧ $ ₂′ (splitAt i₁ w)) = refl
\end{code}
%</rows-to-cols>

%<*cols-to-rows>
\AgdaTarget{cols-to-rows}
\begin{code}
cols-to-rows : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ i₁ m₁) (f₂ : ℂ i₂ m₂) (g₁ : ℂ m₁ o₁) (g₂ : ℂ m₂ o₂)
               → (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂) ≋ (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂)
cols-to-rows f₁ f₂ g₁ g₂ = ≋-sym (rows-to-cols f₁ f₂ g₁ g₂)
\end{code}
%</cols-to-rows>
