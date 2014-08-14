\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using ([_]; _∷_)
open import Data.Bool using (false; true; not; _∧_; _∨_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (W)
open import PiWare.Gates Atomic-B using (Gates)
\end{code}


\begin{code}
private
\end{code}
  %<*cardinality>
  \begin{code}
  |BoolTrio|-1  = 4
  |BoolTrio|    = suc |BoolTrio|-1
  \end{code}
  %</cardinality>

  %<*pattern-synonyms>
  \begin{code}
  pattern FalseConst#  = Fz
  pattern TrueConst#   = Fs Fz
  pattern Not#         = Fs (Fs Fz)
  pattern And#         = Fs (Fs (Fs Fz))
  pattern Or#          = Fs (Fs (Fs (Fs Fz)))
  pattern Absurd# n    = Fs (Fs (Fs (Fs (Fs n))))
  \end{code}
  %</pattern-synonyms>

  %<*ins-outs>
  \begin{code}
  |in| |out| : Fin |BoolTrio| → ℕ
  |in| = λ { FalseConst# → 0; TrueConst# → 0; Not# → 1; And# → 2; Or# → 2; (Absurd# ()) }
  |out| _ = 1
  \end{code}
  %</ins-outs>

  %<*spec>
  \begin{code}
  spec : (g : Fin |BoolTrio|) → (W (|in| g) → W (|out| g))
  spec FalseConst#  = const [ false ]
  spec TrueConst#   = const [ true  ]
  spec Not#         = λ { (x ∷ ε)      → [ not x ] }
  spec And#         = λ { (x ∷ y ∷ ε)  → [ x ∧ y ] }
  spec Or#          = λ { (x ∷ y ∷ ε)  → [ x ∨ y ] }
  spec (Absurd# ())
  \end{code}
  %</spec>

%<*BoolTrio>
\begin{code}
BoolTrio : Gates
BoolTrio = record {
      |Gates|-1  = |BoolTrio|-1
    ; |in|       = |in|
    ; |out|      = |out|
    ; spec       = spec
    }
\end{code}
%</BoolTrio>
