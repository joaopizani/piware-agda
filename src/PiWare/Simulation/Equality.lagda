\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation.Equality {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_; _$_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; uncurry′)

open import Data.Vec.Equality using () renaming (module PropositionalEquality to VPE)
open VPE using (to-≡; _≈_) renaming (refl to reflᵥ; sym to symᵥ; trans to transᵥ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relation.Binary.Indexed.Core using (Setoid; IsEquivalence)
import Relation.Binary.Indexed.EqReasoning as IdxEqReasoning

open import PiWare.Circuit {Gt = Gt} using (ℂ)
open import PiWare.Simulation Gt using (⟦_⟧)
open Atomic At using (W)
\end{code}


%<*Circ-eq-sim-one-input>
\AgdaTarget{\_≅\_}
\begin{code}
_≅_ : ∀ {i o₁ o₂} → ℂ i o₁ → ℂ i o₂ → Set
_≅_ c₁ c₂ = ∀ w → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ w

infixl 3 _≅_
\end{code}
%</Circ-eq-sim-one-input>

%<*Circ-eq-sim-equal-inputs>
\AgdaTarget{\_≊\_}
\begin{code}
_≊_ : ∀ {i o i′ o′} → ℂ i o → ℂ i′ o′ → Set
_≊_ {i} {_} {i′} {_} c₁ c₂ = ∀ {w : W i} {w′ : W i′} → w ≈ w′ → ⟦ c₁ ⟧ w ≈ ⟦ c₂ ⟧ w′

infixl 3 _≊_
\end{code}
%</Circ-eq-sim-equal-inputs>

%<*Circ-eq-sim>
\AgdaTarget{\_≋\_}
\begin{code}
infixl 3 _≋_

data _≋_ {i₁ o₁ i₂ o₂} : ℂ i₁ o₁ → ℂ i₂ o₂ → Set where
  refl≋ : {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} (i≡ : i₁ ≡ i₂) → c₁ ≊ c₂ → c₁ ≋ c₂
\end{code}
%</Circ-eq-sim>


%<*Circ-eq-one-input-to-equal>
\AgdaTarget{≅⇒≋}
\begin{code}
≅⇒≋ : ∀ {i o₁ o₂} {c₁ : ℂ i o₁} {c₂ : ℂ i o₂} → c₁ ≅ c₂ → c₁ ≋ c₂
≅⇒≋ {i} {c₁ = c₁} {c₂} c₁≅c₂ = refl≋ refl f
  where f : {w₁ w₂ : W i} → w₁ ≈ w₂ → ⟦ c₁ ⟧ w₁ ≈ ⟦ c₂ ⟧ w₂
        f w₁≈w₂ rewrite to-≡ w₁≈w₂ = c₁≅c₂ _
\end{code}
%</Circ-eq-one-input-to-equal>


%<*Circ-eq-refl>
\AgdaTarget{≋-refl}
\begin{code}
≋-refl : ∀ {i o} {c : ℂ i o} → c ≋ c
≋-refl = ≅⇒≋ (λ _ → reflᵥ _)
\end{code}
%</Circ-eq-refl>

%<*Circ-eq-sym>
\AgdaTarget{≋-sym}
\begin{code}
≋-sym : ∀ {i o i′ o′} {c₁ : ℂ i o} {c₂ : ℂ i′ o′} → c₁ ≋ c₂ → c₂ ≋ c₁
≋-sym (refl≋ refl c₁≊c₂) = ≅⇒≋ (symᵥ ∘ c₁≊c₂ ∘ symᵥ ∘ reflᵥ)
\end{code}
%</Circ-eq-sym>

%<*Circ-eq-trans>
\AgdaTarget{≋-trans}
\begin{code}
≋-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {c₁ : ℂ i₁ o₁} {c₂ : ℂ i₂ o₂} {c₃ : ℂ i₃ o₃} → c₁ ≋ c₂ → c₂ ≋ c₃ → c₁ ≋ c₃
≋-trans (refl≋ refl c₁≊c₂) (refl≋ refl c₂≊c₃) = ≅⇒≋ (λ w → transᵥ (c₁≊c₂ $ reflᵥ w) (c₂≊c₃ $ reflᵥ w))
\end{code}
%</Circ-eq-trans>

%<*Circ-eq-isEquivalence>
\AgdaTarget{≋-isEquivalence}
\begin{code}
≋-isEquivalence : IsEquivalence (uncurry′ ℂ) _≋_
≋-isEquivalence = record
  { refl  = ≋-refl
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }
\end{code}
%</Circ-eq-isEquivalence>

%<*Circ-setoid>
\AgdaTarget{≋-setoid}
\begin{code}
≋-setoid : Setoid (ℕ × ℕ) _ _
≋-setoid = record
  { Carrier       = uncurry′ ℂ
  ; _≈_           = _≋_
  ; isEquivalence = ≋-isEquivalence
  }
\end{code}
%</Circ-setoid>


%<*Circ-eq-reasoning>
\AgdaTarget{\_≋⟨\_⟩\_,\_≡⟨\_⟩\_,\_≡⟨⟩\_}
\begin{code}
open IdxEqReasoning ≋-setoid public
  using (begin_; _∎)
  renaming ( _≈⟨_⟩_ to _≋⟨_⟩_
           ; _≡⟨_⟩_ to _≡⟨_⟩_
           ; _≡⟨⟩_  to _≡⟨⟩_
           )
\end{code}
%</Circ-eq-reasoning>
