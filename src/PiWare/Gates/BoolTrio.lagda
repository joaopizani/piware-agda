\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; [_]; _∷_)
open import Data.Bool using (false; true; not; _∧_; _∨_) renaming (Bool to B)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (W)
open import PiWare.Gates Atomic-B using (Gates)
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

%<*ins-outs-decl>
\begin{code}
|in| |out| : Fin |BoolTrio| → ℕ
\end{code}
%</ins-outs-decl>
%<*ins-outs-def>
\begin{code}
|in| FalseConst#  = 0
|in| TrueConst#   = 0
|in| Not#         = 1
|in| And#         = 2
|in| Or#          = 2
|in| (Absurd# ())

|out| _ = 1
\end{code}
%</ins-outs-def>

%<*spec-gates-decl>
\begin{code}
spec-false spec-true  : W 0 → W 1
spec-not              : W 1 → W 1
spec-and spec-or      : W 2 → W 1
\end{code}
%</spec-gates-decl>
%<*spec-gates-def>
\begin{code}
spec-false  _            = [ false  ]
spec-true   _            = [ true   ]
spec-not    (x ∷ ε)      = [ not x  ]
spec-and    (x ∷ y ∷ ε)  = [ x ∧ y  ]
spec-or     (x ∷ y ∷ ε)  = [ x ∨ y  ]
\end{code}
%</spec-gates-def>

%<*specs-BoolTrio-decl>
\begin{code}
specs-BoolTrio : (g : Fin |BoolTrio|) → (W (|in| g) → W (|out| g))
\end{code}
%</specs-BoolTrio-decl>
%<*specs-BoolTrio-def>
\begin{code}
specs-BoolTrio FalseConst#  = spec-false
specs-BoolTrio TrueConst#   = spec-true
specs-BoolTrio Not#         = spec-not
specs-BoolTrio And#         = spec-and
specs-BoolTrio Or#          = spec-or
specs-BoolTrio (Absurd# ())
\end{code}
%</specs-BoolTrio-def>

%<*BoolTrio>
\begin{code}
BoolTrio : Gates
BoolTrio = record  { |Gates|  = |BoolTrio|
                   ; |in|     = |in|
                   ; |out|    = |out|
                   ; spec     = specs-BoolTrio }
\end{code}
%</BoolTrio>
