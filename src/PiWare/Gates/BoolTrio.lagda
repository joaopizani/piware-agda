\begin{code}
module PiWare.Gates.BoolTrio where

open import Function using (const)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; [_]) renaming (_∷_ to _◁_; [] to ε)
open import Data.Bool using (false; true; not; _∧_; _∨_) renaming (Bool to B)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_) renaming ([] to ε; [_] to [_]l)
open import Data.String using (String; _++_)
open import Data.Maybe using (nothing)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (W)
open import PiWare.Gates Atomic-B using (Gates)

import VHDL.AST as VHDL using ( EntityDecl; ArchBody; SigDecl; BasicIdent
                              ; In; Out; NSimple; CSSAStmt; PrimName; WformCon; Expr; Not; And; Or)
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

\begin{code}
spec-not : Vec B 1 → Vec B 1
spec-and spec-or : Vec B 2 → Vec B 1

spec-not (x ◁ ε)     = [ not x ]
spec-and (x ◁ y ◁ ε) = [ x ∧ y ]
spec-or  (x ◁ y ◁ ε) = [ x ∨ y ]
\end{code}

%<*spec>
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

%<*syn>
\begin{code}
nullarySigs unarySigs binarySigs : List VHDL.SigDecl

nullarySigs = [ record { ident = VHDL.BasicIdent "out";  mode = VHDL.Out;  typeMark = VHDL.BasicIdent "Boolean" } ]l

unarySigs =   record { ident = VHDL.BasicIdent "a";   mode = VHDL.In;  typeMark = VHDL.BasicIdent "Boolean" }
              ∷ record { ident = VHDL.BasicIdent "out"; mode = VHDL.Out; typeMark = VHDL.BasicIdent "Boolean" }
              ∷ ε

binarySigs  =   record { ident = VHDL.BasicIdent "a";   mode = VHDL.In;  typeMark = VHDL.BasicIdent "Boolean" }
              ∷ record { ident = VHDL.BasicIdent "b";   mode = VHDL.In;  typeMark = VHDL.BasicIdent "Boolean" }
              ∷ record { ident = VHDL.BasicIdent "out"; mode = VHDL.Out; typeMark = VHDL.BasicIdent "Boolean" }
              ∷ ε

binaryArch : String → (VHDL.Expr → VHDL.Expr → VHDL.Expr) → VHDL.ArchBody
binaryArch s op = record {
    ident = VHDL.BasicIdent (s ++ "-Behaviour")
  ; name  = VHDL.NSimple (VHDL.BasicIdent s)
  ; blkDecls  = ε
  ; concStmts =
      [ VHDL.CSSAStmt (record { target  = (VHDL.NSimple (VHDL.BasicIdent "out"))
                              ; consigs = (record { main = VHDL.WformCon (record { expr = op (VHDL.PrimName (VHDL.NSimple (VHDL.BasicIdent "a")))
                                                                                             (VHDL.PrimName (VHDL.NSimple (VHDL.BasicIdent "b")))
                                                                                 ; after = nothing } ∷ ε)
                                                  ; when = nothing
                                                  ; elses = ε }) })
      ]l
  }

nullaryArch : String → VHDL.Expr → VHDL.ArchBody
nullaryArch s e = record {
    ident = VHDL.BasicIdent (s ++ "-Behaviour")
  ; name  = VHDL.NSimple (VHDL.BasicIdent s)
  ; blkDecls  = ε
  ; concStmts =
      [ VHDL.CSSAStmt (record { target  = (VHDL.NSimple (VHDL.BasicIdent "out"))
                              ; consigs = (record { main = VHDL.WformCon (record { expr = e; after = nothing } ∷ ε)
                                                  ; when = nothing
                                                  ; elses = ε }) })
      ]l
  }

notArch : VHDL.ArchBody
notArch = record {
    ident = VHDL.BasicIdent "BT-NOT-Behaviour"
  ; name  = VHDL.NSimple (VHDL.BasicIdent "BT-NOT")
  ; blkDecls  = ε
  ; concStmts =
      [ VHDL.CSSAStmt (record { target  = (VHDL.NSimple (VHDL.BasicIdent "out"))
                              ; consigs = (record {main = VHDL.WformCon (record {expr = VHDL.Not (VHDL.PrimName (VHDL.NSimple (VHDL.BasicIdent "a")))
                                                                                ; after = nothing } ∷ ε)
                                                  ; when = nothing
                                                  ; elses = ε }) })
      ]l
  }

syn : (g : Fin |BoolTrio|) → VHDL.EntityDecl × VHDL.ArchBody
syn FalseConst# =   record { ident = VHDL.BasicIdent "BT-FALSECONST";  sigDecls = nullarySigs }
                  , nullaryArch "BT-FALSECONST" (VHDL.PrimName (VHDL.NSimple (VHDL.BasicIdent "false")))

syn TrueConst#  =   record { ident = VHDL.BasicIdent "BT-TRUECONST";  sigDecls = nullarySigs }
                  , nullaryArch "BT-TRUECONST" (VHDL.PrimName (VHDL.NSimple (VHDL.BasicIdent "true")))

syn Not#        = record { ident = VHDL.BasicIdent "BT-NOT"; sigDecls = unarySigs }  , notArch
syn And#        = record { ident = VHDL.BasicIdent "BT-AND"; sigDecls = binarySigs } , binaryArch "BT-AND" VHDL.And
syn Or#         = record { ident = VHDL.BasicIdent "BT-OR";  sigDecls = binarySigs } , binaryArch "BT-OR" VHDL.Or

syn (Absurd# ())
\end{code}
%</syn>

%<*BoolTrio>
\begin{code}
BoolTrio : Gates
BoolTrio = record {
      |Gates| = |BoolTrio|
    ; |in|    = |in|
    ; |out|   = |out|
    ; spec    = spec
    ; syn     = syn
    }
\end{code}
%</BoolTrio>
