\begin{code}
module Data.CausalStream where

open import Level using (_⊔_)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (List; _∷_) renaming ([] to ε)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.List.NonEmpty.Extra using (tails⁺)

open import Coinduction using (♯_; ♭)
open import Data.Stream using (Stream; _∷_)
\end{code}


-- Causal context: present × past
%<*causal-context>
\AgdaTarget{Γᶜ}
\begin{code}
Γᶜ : ∀ {ℓ} (α : Set ℓ) → Set ℓ
Γᶜ = List⁺
\end{code}
%</causal-context>


-- Causal step function: causal context → next value
%<*causal-step>
\AgdaTarget{\_⇒ᶜ\_}
\begin{code}
_⇒ᶜ_ : ∀ {a b} (α : Set a) (β : Set b) → Set (a ⊔ b)
α ⇒ᶜ β = Γᶜ α → β
\end{code}
%</causal-step>


%<*pasts>
\AgdaTarget{pasts}
\begin{code}
pasts : ∀ {ℓ} {α : Set ℓ} → Γᶜ α → List⁺ (Γᶜ α)
pasts = tails⁺
\end{code}
%</pasts>


%<*causal-patterns>
\AgdaTarget{\_≻\_, \_≺\_}
\begin{code}
infixl 5 _≻_
infixr 5 _≺_

pattern _≻_ xs⁻ x = x ∷ xs⁻
pattern _≺_ x xs⁺ = x ∷ xs⁺
\end{code}
%</causal-patterns>

%<*run-causal>
\AgdaTarget{runᶜ}
\begin{code}
runᶜ : ∀ {α β : Set} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ≺ x⁺) = runᶜ' f (ε ≻ x⁰) (♭ x⁺)
  where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → Γᶜ α → Stream α → Stream β
        runᶜ' f (x⁻ ≻ x⁰) (x¹ ≺ x⁺) = f (x⁻ ≻ x⁰) ∷ ♯ runᶜ' f (x⁻ ≻ x⁰ ≻ x¹) (♭ x⁺)
\end{code}
%</run-causal>
