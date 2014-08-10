\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Patterns {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (zero; suc; _*_)

open import PiWare.Circuit.Core Gt using (ℂ'; Nil; _|'_)
\end{code}


\begin{code}
pars' : ∀ {k m n} → ℂ' m n → ℂ' (k * m) (k * n)
pars' {zero}  c' = Nil
pars' {suc k} c' = c' |' pars' {k} c'
\end{code}
