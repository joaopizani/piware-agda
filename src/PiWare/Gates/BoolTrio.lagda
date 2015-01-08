\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; _∷_; [_]) renaming ([] to ε)
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
pattern ⊥#         = Fz
pattern ⊤#         = Fs Fz
pattern ¬#         = Fs (Fs Fz)
pattern ∧#         = Fs (Fs (Fs Fz))
pattern ∨#         = Fs (Fs (Fs (Fs Fz)))
pattern Absurd# n  = Fs (Fs (Fs (Fs (Fs n))))
\end{code}
%</pattern-synonyms>

%<*ins-outs>
\begin{code}
|in| |out| : Fin |BoolTrio| → ℕ
|out| _  = 1
|in|     = λ { ⊥# → 0; ⊤# → 0; ¬# → 1; ∧# → 2; ∨# → 2; (Absurd# ()) }
\end{code}
%</ins-outs>

%<*specs-type>
\begin{code}
spec-¬#          : Vec B 1 → Vec B 1
spec-∧# spec-∨#  : Vec B 2 → Vec B 1
\end{code}
%</specs-type>

%<*specs-def>
\AgdaTarget{spec-¬\#, spec-∧\#, spec-∨\#}
\begin{code}
spec-¬# (x ∷ ε)      = [ not x ]
spec-∧# (x ∷ y ∷ ε)  = [ x ∧ y ]
spec-∨# (x ∷ y ∷ ε)  = [ x ∨ y ]
\end{code}
%</specs-def>

%<*spec>
\AgdaTarget{spec}
\begin{code}
spec : (g : Fin |BoolTrio|) → (W (|in| g) → W (|out| g))
spec ⊥# = const [ false ]
spec ⊤# = const [ true  ]
spec ¬# = spec-¬#
spec ∧# = spec-∧#
spec ∨# = spec-∨#
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
