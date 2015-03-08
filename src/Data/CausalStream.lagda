\begin{code}
module Data.CausalStream where

open import Level using (_⊔_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
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


-- Causal step: causal context → next value
%<*causal-step>
\AgdaTarget{\_⇒ᶜ\_}
\begin{code}
_⇒ᶜ_ : ∀ {a b} (α : Set a) (β : Set b) → Set (a ⊔ b)
α ⇒ᶜ β = Γᶜ α → β
\end{code}
%</causal-step>


%<*causal-tails>
\begin{code}
tailsᶜ : ∀ {ℓ} {α : Set ℓ} → Γᶜ α → List⁺ (Γᶜ α)
tailsᶜ = tails⁺
\end{code}
%</causal-tails>


%<*run-causal>
\AgdaTarget{runᶜ}
\begin{code}
runᶜ : ∀ {α β : Set} → (α ⇒ᶜ β) → (Stream α → Stream β)
runᶜ f (x⁰ ∷ x⁺) = runᶜ' f ((x⁰ ∷ []) , ♭ x⁺)
  where runᶜ' : ∀ {α β} → (α ⇒ᶜ β) → (Γᶜ α × Stream α) → Stream β
        runᶜ' f ((x⁰ ∷ x⁻) , (x¹ ∷ x⁺)) = f (x⁰ ∷ x⁻) ∷ ♯ runᶜ' f ((x¹ ∷ x⁰ ∷ x⁻) , ♭ x⁺)
\end{code}
%</run-causal>
