\begin{code}
module PiWare.Atom.Bool where

open import Data.Bool using (true; false) renaming (Bool to B)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Atom using (Atomic)
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

 %<*nToBool-decl>
 \begin{code}
 n→B : Fin |B| → B
 B→n : B → Fin |B|
 \end{code}
 %</nToBool-decl>
 %<*nToBool-def>
 \begin{code}
 n→B = λ { False# → false;   True#  → true;  (Absurd# ()) }
 B→n = λ { false  → False#;  true   → True# }
 \end{code}
 %</nToBool-def>
 
 %<*inv-Bool-decl>
 \begin{code}
 inv-left-B : ∀ i → B→n (n→B i) ≡ i
 inv-right-B : ∀ b → n→B (B→n b) ≡ b
 \end{code}
 %</inv-Bool-decl>
 %<*inv-Bool-def>
 \begin{code}
 inv-left-B   = λ { False#  → refl;  True#  → refl;  (Absurd# ()) }
 inv-right-B  = λ { false   → refl;  true   → refl }
 \end{code}
 %</inv-Bool-def>


%<*Atomic-Bool>
\begin{code}
Atomic-B = record  { Atom       = B
                   ; |Atom|-1   = |B|-1
                   ; n→atom     = n→B
                   ; atom→n     = B→n
                   ; inv-left   = inv-left-B
                   ; inv-right  = inv-right-B }
\end{code}
%</Atomic-Bool>
