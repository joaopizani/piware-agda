\begin{code}
module Data.CausalStream where

open import Data.Product using (_,_; uncurry′)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺) renaming ([_] to [_]⁺)
\end{code}


-- Causal context: past × present
%<*causal-context>
\begin{code}
Γᶜ : (α : Set) → Set
Γᶜ = List⁺
\end{code}
%</causal-context>

-- Causal step: causal context → next value
%<*causal-step>
\begin{code}
_⇒ᶜ_ : (α β : Set) → Set
α ⇒ᶜ β = Γᶜ α → β
\end{code}
%</causal-step>

-- Needs to use the trick with tails' and uncurry to "convince" the termination checker
%<*tails-nonempty>
\begin{code}
tails⁺ : ∀ {α} → Γᶜ α → List⁺ (List⁺ α)
tails⁺ {α} = uncurry′ tails⁺'
    where tails⁺' : α → List α → List⁺ (List⁺ α)
          tails⁺' x₀ []        = [ x₀ , [] ]⁺
          tails⁺' x₀ (x₁ ∷ xs) = let (t₁ , ts) = tails⁺' x₁ xs  in  (x₀ , x₁ ∷ xs) , (t₁ ∷ ts)
\end{code}
%</tails-nonempty>
