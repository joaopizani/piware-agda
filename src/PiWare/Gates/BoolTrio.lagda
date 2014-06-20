\begin{code}
module PiWare.Gates.BoolTrio where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using ([_]) renaming (_∷_ to _◁_)
open import Data.Bool using (not; _∧_; _∨_)

open import PiWare.Atom.Bool using (Atomic-𝔹)
open import PiWare.Synthesizable Atomic-𝔹 using (𝕎)
open import PiWare.Gates Atomic-𝔹
\end{code}


\begin{code}
private
\end{code}
  -- 0 → NOT,  1 → AND,  2 → OR
  \begin{code}
  |BoolTrio|-1 : ℕ
  |BoolTrio|-1 = 2
  
  |BoolTrio| = suc |BoolTrio|-1
  \end{code}

  \begin{code}
  pattern F0 = Fz
  pattern F1 = Fs F0
  pattern F2 = Fs F1
  pattern F3 n = Fs (Fs (Fs n))
  \end{code}

  \begin{code}
  ins outs : Fin |BoolTrio| → ℕ
  ins    = λ { F0 → 1;  F1 → 2;  F2 → 2;  (F3 ()) }
  outs _ = 1
  \end{code}
  
  \begin{code}
  spec : (g : Fin |BoolTrio|) → (𝕎 (ins g) → 𝕎 (outs g))
  spec F0 = λ { (x ◁ ε) → [ not x ] }
  spec F1 = λ { (x ◁ y ◁ ε) → [ x ∧ y ] }
  spec F2 = λ { (x ◁ y ◁ ε) → [ x ∨ y ] }
  spec (F3 ())
  \end{code}
  
\begin{code}
BoolTrio : Gates
BoolTrio = record {
      |Gates|-1 = |BoolTrio|-1
    ; ins       = ins
    ; outs      = outs
    ; spec      = spec
    }
\end{code}
