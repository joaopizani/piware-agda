\begin{code}
module Report.ChapterPiWare where

open import Data.List using (List)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)

open import Coinduction using (♯_; ♭)
open import Data.Stream using (Stream; _∷_)
\end{code}


%<*stream-tail>
\begin{code}
tail : ∀ {α} → Stream α → Stream α
tail (x ∷ xs) = ♭ xs
\end{code}
%</stream-tail>


\begin{code}
postulate seggregateStream-bogus : {α β : Set} → Stream (α ⊎ β) → List α × List β
\end{code}

%<*seggregateStream-decl>
\begin{code}
seggregateStream : ∀ {α β} → Stream (α ⊎ β) → List α × List β
\end{code}
%</seggregateStream-decl>
%<*seggregateStream-def>
\begin{code}
seggregateStream = seggregateStream-bogus
\end{code}
%</seggregateStream-def>
