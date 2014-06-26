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
  %<*size>
  \begin{code}
  |BoolTrio|-1 : ℕ
  |BoolTrio|-1 = 2
  
  |BoolTrio| = suc |BoolTrio|-1
  \end{code}
  %</size>

  %<*pattern-synonyms>
  \begin{code}
  pattern Not# = Fz
  pattern And# = Fs Fz
  pattern Or#  = Fs (Fs Fz)
  pattern Absurd# n = Fs (Fs (Fs n))
  \end{code}
  %</pattern-synonyms>

  %<*ins-outs>
  \begin{code}
  ins outs : Fin |BoolTrio| → ℕ
  ins    = λ { Not# → 1;  And# → 2;  Or# → 2;  (Absurd# ()) }
  outs _ = 1
  \end{code}
  %</ins-outs>

  %<*spec>
  \begin{code}
  spec : (g : Fin |BoolTrio|) → (𝕎 (ins g) → 𝕎 (outs g))
  spec Not# = λ { (x ◁ ε) → [ not x ] }
  spec And# = λ { (x ◁ y ◁ ε) → [ x ∧ y ] }
  spec Or#  = λ { (x ◁ y ◁ ε) → [ x ∨ y ] }
  spec (Absurd# ())
  \end{code}
  %</spec>

%<*BoolTrio>
\begin{code}
BoolTrio : Gates
BoolTrio = record {
      |Gates|-1 = |BoolTrio|-1
    ; ins       = ins
    ; outs      = outs
    ; spec      = spec
    }
\end{code}
%</BoolTrio>
