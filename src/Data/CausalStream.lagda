\begin{code}
module Data.CausalStream where

open import Data.Product using (_,_; uncurry′)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺) renaming ([_] to [_]⁺)

\end{code}

-- Causal context: past × present
\begin{code}
Γᶜ : (α : Set) → Set
Γᶜ = List⁺
\end{code}

-- Causal stream step: causal context → next future value
\begin{code}
_⇒ᶜ_ : (α β : Set) → Set
α ⇒ᶜ β = Γᶜ α → β
\end{code}

-- Needs to use the trick with tails' and uncurry to "convince" the termination checker
\begin{code}
tails⁺ : ∀ {α} → Γᶜ α → List⁺ (List⁺ α)
tails⁺ {α} = uncurry′ tails⁺'
    where tails⁺' : α → List α → List⁺ (List⁺ α)
          tails⁺' x₀ []        = [ x₀ , [] ]⁺
          tails⁺' x₀ (x₁ ∷ xs) = let (t₁ , ts) = tails⁺' x₁ xs  in  (x₀ , x₁ ∷ xs) , (t₁ ∷ ts)
\end{code}
