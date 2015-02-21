\begin{code}
module Data.CausalStream where

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming ([_] to [_]⁺)

open import Data.List.NonEmpty.Extra using (uncurry⁺)
\end{code}


-- Causal context: present × past
%<*causal-context>
\AgdaTarget{Γᶜ}
\begin{code}
Γᶜ : (α : Set) → Set
Γᶜ = List⁺
\end{code}
%</causal-context>


-- Causal step: causal context → next value
%<*causal-step>
\AgdaTarget{\_⇒ᶜ\_}
\begin{code}
_⇒ᶜ_ : (α β : Set) → Set
α ⇒ᶜ β = Γᶜ α → β
\end{code}
%</causal-step>


-- Needs to use the trick with tails⁺' and uncurry⁺ to "convince" the termination checker
%<*tails-nonempty>
\AgdaTarget{tails⁺}
\begin{code}
tails⁺ : ∀ {α} → Γᶜ α → List⁺ (Γᶜ α)
tails⁺ {α} = uncurry⁺ tails⁺'
    where tails⁺' : α → List α → List⁺ (Γᶜ α)
          tails⁺' x₀ []        = [ x₀ ∷ [] ]⁺
          tails⁺' x₀ (x₁ ∷ xs) = let (t₁ ∷ ts) = tails⁺' x₁ xs  in  (x₀ ∷ x₁ ∷ xs) ∷ (t₁ ∷ ts)
\end{code}
%</tails-nonempty>
