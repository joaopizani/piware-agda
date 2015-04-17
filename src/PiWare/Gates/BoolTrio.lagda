\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (false; true; not; _∧_; _∨_) renaming (Bool to B)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using ([_]) renaming (_∷_ to _◁_; [] to ε)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Interface using (Ix)
open import PiWare.Gates Atomic-B using (Gates)
open import PiWare.Atom using (module Atomic)
open Atomic Atomic-B using (W)
\end{code}


%<*cardinality>
\AgdaTarget{|BoolTrio|}
\begin{code}
|BoolTrio| = 5
\end{code}
%</cardinality>

%<*pattern-synonyms>
\AgdaTarget{⊥ℂ\#, ⊤ℂ\#, ¬ℂ\#, ∧ℂ\#, ∨ℂ\#, Absurd\#}
\begin{code}
pattern ⊥ℂ#       = Fz
pattern ⊤ℂ#       = Fs Fz
pattern ¬ℂ#       = Fs (Fs Fz)
pattern ∧ℂ#       = Fs (Fs (Fs Fz))
pattern ∨ℂ#       = Fs (Fs (Fs (Fs Fz)))
pattern Absurd# n = Fs (Fs (Fs (Fs (Fs n))))
\end{code}
%</pattern-synonyms>

%<*ins-outs>
\begin{code}
|in| |out| : Fin |BoolTrio| → Ix
|out| _ = 1

|in| ⊥ℂ#          = 0
|in| ⊤ℂ#          = 0
|in| ¬ℂ#          = 1
|in| ∧ℂ#          = 2
|in| ∨ℂ#          = 2
|in| (Absurd# ())
\end{code}
%</ins-outs>

%<*specs>
\AgdaTarget{spec-not, spec-and, spec-or}
\begin{code}
spec-not          : W 1 → W 1
spec-and spec-or  : W 2 → W 1
spec-not (x ◁ ε)     = [ not x ]
spec-and (x ◁ y ◁ ε) = [ x ∧ y ]
spec-or  (x ◁ y ◁ ε) = [ x ∨ y ]
\end{code}
%</specs>

%<*spec>
\AgdaTarget{spec}
\begin{code}
spec : ∀ g → (W (|in| g) → W (|out| g))
spec ⊥ℂ#          = const [ false ]
spec ⊤ℂ#          = const [ true  ]
spec ¬ℂ#          = spec-not
spec ∧ℂ#          = spec-and
spec ∨ℂ#          = spec-or
spec (Absurd# ())
\end{code}
%</spec>


%<*BoolTrio>
\AgdaTarget{BoolTrio}
\begin{code}
BoolTrio : Gates
BoolTrio = record
  { |Gates| = |BoolTrio|
  ; |in|    = |in|
  ; |out|   = |out|
  ; spec    = spec
  }
\end{code}
%</BoolTrio>
