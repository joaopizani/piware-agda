\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Function using (id; _∘_; _$_)
open import Data.Nat.Base using (_+_)
open import Data.Product using (_,_)
open import Data.Vec using (splitAt)

open import Data.Nat.Properties.Simple using (+-right-identity; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; setoid; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_; _≡⟨⟩_)

open import Data.Vec.Equality using (module PropositionalEquality)
open PropositionalEquality using (_≈_; to-≡; from-≡; _++-cong_) renaming (refl to reflᵥ)
open import Data.Vec.Properties using (module UsingVectorEquality)
open module X {a} {α : Set a} = UsingVectorEquality (setoid α) using (xs++[]=xs)

open import Data.Vec.Extra using (₁; ₂′)
open import Data.Vec.Properties.Extra
  using (proj₁∘splitAt-last≈; ++-assoc; ++-assoc-split₁; ++-assoc-split₂; ++-assoc-split₃; splitAt-++)

open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Circuit using (ℂ; _⟫_; _∥_)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWare.Simulation.Equality Gt using (_≅_; _≋_; refl≋; ≅⇒≋; ≋-sym)
open import PiWare.Simulation.Properties.Plugs Gt using (id⤨-id)
\end{code}


\begin{code}
infixl 4 _⟫-cong_
\end{code}
%<*seq-cong>
\AgdaTarget{⟫-cong}
\begin{code}
_⟫-cong_ : ∀ {i₁ i₂ m₁ m₂ o₁ o₂} {c₁ : ℂ i₁ m₁} {d₁ : ℂ m₁ o₁} {c₂ : ℂ i₂ m₂} {d₂ : ℂ m₂ o₂}
           → c₁ ≋ c₂ → d₁ ≋ d₂ → (c₁ ⟫ d₁) ≋ (c₂ ⟫ d₂)
(refl≋ refl c₁≊c₂) ⟫-cong (refl≋ refl d₁≊d₂) = ≅⇒≋ (d₁≊d₂ ∘ c₁≊c₂ ∘ reflᵥ)
\end{code}
%</seq-cong>


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


\begin{code}
infixr 5 _∥-cong_
\end{code}
%<*par-cong>
\AgdaTarget{_∥-cong_}
\begin{code}
_∥-cong_ : ∀ {i₁ o₁ j₁ p₁ i₂ o₂ j₂ p₂} {c₁ : ℂ i₁ o₁} {d₁ : ℂ j₁ p₁} {c₂ : ℂ i₂ o₂} {d₂ : ℂ j₂ p₂}
           → c₁ ≋ c₂ → d₁ ≋ d₂ → (c₁ ∥ d₁) ≋ (c₂ ∥ d₂)
(refl≋ refl c₁≊c₂) ∥-cong (refl≋ refl d₁≊d₂) = ≅⇒≋ (λ _ → (c₁≊c₂ (reflᵥ _)) ++-cong (d₁≊d₂ (reflᵥ _)))
\end{code}
%</par-cong>


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
