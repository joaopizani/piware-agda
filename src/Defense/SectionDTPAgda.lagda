\begin{code}
module Defense.SectionDTPAgda where

open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋)
open import Data.Product using (_×_; _,_)
\end{code}


%<*add>
\begin{code}
add : ℕ → ℕ → ℕ
add zero      y  = y
add (suc x′)  y  = suc (add x′ y)
\end{code}
%</add>


\begin{code}
{-# NO_TERMINATION_CHECK #-}
\end{code}
%<*silly>
\begin{code}
silly : ℕ → ℕ
silly zero      = zero
silly (suc n′)  = silly ⌊ n′ /2⌋
\end{code}
%</silly>
