\begin{code}
module PiWare.Atom.Bool where

open import Data.Bool using (true; false) renaming (Bool to B)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; suc)
open import Data.List using (_∷_) renaming ([] to ε)
open import Data.String using ()

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Atom using (Atomic)

open import VHDL.AST as VHDL using (TypeDecl; Expr; BasicIdent; TDE; PrimName; NSimple)
\end{code}


\begin{code}
private
\end{code}
  %<*cardinality>
  \begin{code}
  |B|-1 = 1
  |B| = suc |B|-1
  \end{code}
  %</cardinality>

  %<*pattern-synonyms>
  \begin{code}
  pattern False#    = Fz
  pattern True#     = Fs Fz
  pattern Absurd# n = Fs (Fs n)
  \end{code}
  %</pattern-synonyms>

  %<*nToBool>
  \begin{code}
  n→B : Fin |B| → B
  n→B = λ { False# → false;  True# → true;  (Absurd# ()) }
  \end{code}
  %</nToBool>
  
  %<*boolToN>
  \begin{code}
  B→n : B → Fin |B|
  B→n = λ { false → False#;  true → True# }
  \end{code}
  %</boolToN>
  
  %<*inv-left-Bool>
  \begin{code}
  inv-left-B : ∀ i → B→n (n→B i) ≡ i
  inv-left-B = λ { False# → refl;  True# → refl;  (Absurd# ()) }
  \end{code}
  %</inv-left-Bool>

  %<*inv-right-Bool>
  \begin{code}
  inv-right-B : ∀ b → n→B (B→n b) ≡ b
  inv-right-B = λ { false → refl;  true → refl }
  \end{code}
  %</inv-right-Bool>

  %<*BoolSyn>
  \begin{code}
  BoolSyn : VHDL.TypeDecl
  BoolSyn = record { ident = BasicIdent "Boolean"
                   ; def   = TDE (record { idents = identFalse ∷ identTrue ∷ ε }) }
      where
          identFalse = BasicIdent "false"
          identTrue  = BasicIdent "true"
  \end{code}
  %</BoolSyn>

  %<*nToBoolSyn>
  \begin{code}
  n→BoolSyn : Fin |B| → VHDL.Expr
  n→BoolSyn False#       = PrimName (NSimple (BasicIdent "false"))
  n→BoolSyn True#        = PrimName (NSimple (BasicIdent "true"))
  n→BoolSyn (Absurd# ())
  \end{code}
  %</nToBoolSyn>


%<*Atomic-Bool>
\begin{code}
Atomic-B : Atomic
Atomic-B = record {
      Atom     = B
    ; |Atom|-1 = |B|-1
    ; n→atom   = n→B
    ; atom→n   = B→n
   
    ; inv-left  = inv-left-B
    ; inv-right = inv-right-B

    ; AtomSyn   = BoolSyn
    ; n→atomSyn = n→BoolSyn
    }
\end{code}
%</Atomic-Bool>
