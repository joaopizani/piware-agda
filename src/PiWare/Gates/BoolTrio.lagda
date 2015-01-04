\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; [_]) renaming (_∷_ to _◁_; [] to ε)
open import Data.Bool using (false; true; not; _∧_; _∨_) renaming (Bool to B)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Gates Atomic-B using (Gates)
open import PiWare.Atom using (module Atomic)
open Atomic Atomic-B using (W)
\end{code}


%<*cardinality>
\begin{code}
|BoolTrio| = 5
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

%<*specs>
\AgdaTarget{spec-not, spec-and, spec-or}
\begin{code}
spec-not          : Vec B 1 → Vec B 1
spec-and spec-or  : Vec B 2 → Vec B 1
spec-not (x ◁ ε)     = [ not x ]
spec-and (x ◁ y ◁ ε) = [ x ∧ y ]
spec-or  (x ◁ y ◁ ε) = [ x ∨ y ]
\end{code}
%</specs>

%<*spec>
\AgdaTarget{spec}
\begin{code}
spec : (g : Fin |BoolTrio|) → (W (|in| g) → W (|out| g))
spec FalseConst#  = const [ false ]
spec TrueConst#   = const [ true  ]
spec Not#         = spec-not
spec And#         = spec-and
spec Or#          = spec-or
spec (Absurd# ())
\end{code}
%</spec>

%<*BoolTrio>
\AgdaTarget{BoolTrio}
\begin{code}
BoolTrio : Gates
BoolTrio = record {
      |Gates| = |BoolTrio|
    ; |in|    = |in|
    ; |out|   = |out|
    ; spec    = spec
    }
\end{code}
%</BoolTrio>
