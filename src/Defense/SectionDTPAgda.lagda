\begin{code}
module Defense.SectionDTPAgda where

open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_)
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


%<*head>
\begin{code}
head : {α : Set} {n : ℕ} → Vec α (suc n) → α
head (x ∷ xs) = x
\end{code}
%</head>


%<*take-decl>
\begin{code}
take : {α : Set} {n : ℕ} (k : ℕ) → Vec α (k + n) → Vec α k
\end{code}
%</take-decl>
%<*take-def>
\begin{code}
take zero    _        = []
take (suc k) (x ∷ xs) = x ∷ take k xs
\end{code}
%</take-def>
