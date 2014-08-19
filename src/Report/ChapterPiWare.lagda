\begin{code}
module Report.ChapterPiWare where

open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Coinduction using (♯_; ♭; ∞)
open import Data.Stream using (Stream; _∷_)
\end{code}


%<*stream-tail>
\begin{code}
tail : ∀ {α} → Stream α → Stream α
tail (x ∷ xs) = ♭ xs
\end{code}
%</stream-tail>


%<*bisimilarity>
\begin{code}
data _≈_ {α : Set} : Stream α → Stream α → Set where
    _∷_ : ∀  {x y xs ys}
             (heads≡ : x ≡ y) (tails≈ : ∞ (♭ xs ≈ ♭ ys)) → (x ∷ xs) ≈ (y ∷ ys)
\end{code}
%</bisimilarity>


\begin{code}
postulate seggregateStream-bogus : {α β : Set} → Stream (α ⊎ β) → Stream α × Stream β
\end{code}

%<*seggregateStream-decl>
\begin{code}
seggregateStream : ∀ {α β} → Stream (α ⊎ β) → Stream α × Stream β
\end{code}
%</seggregateStream-decl>
%<*seggregateStream-def>
\begin{code}
seggregateStream = seggregateStream-bogus
\end{code}
%</seggregateStream-def>
