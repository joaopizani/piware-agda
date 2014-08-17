\begin{code}
module Report.ChapterPiWare where

open import Coinduction using (♯_; ♭)
open import Data.Stream using (Stream; _∷_)
\end{code}


%<*stream-tail>
\begin{code}
tail : ∀ {α} → Stream α → Stream α
tail (x ∷ xs) = ♭ xs
\end{code}
%</stream-tail>

