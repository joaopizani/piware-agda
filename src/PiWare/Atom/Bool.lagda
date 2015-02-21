\begin{code}
module PiWare.Atom.Bool where

open import Data.Bool using (true; false) renaming (Bool to B)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (suc)

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
 \AgdaTarget{False\#, True\#, Absurd\#}
 \begin{code}
 pattern False#    = Fz
 pattern True#     = Fs Fz
 pattern Absurd# n = Fs (Fs n)
 \end{code}
 %</pattern-synonyms>

 %<*nToBool>
 \AgdaTarget{n→B}
 \begin{code}
 n→B : Fin |B| → B
 n→B = λ { False# → false;  True# → true;  (Absurd# ()) }
 \end{code}
 %</nToBool>
 
 %<*boolToN>
 \AgdaTarget{B→n}
 \begin{code}
 B→n : B → Fin |B|
 B→n = λ { false → False#;  true → True# }
 \end{code}
 %</boolToN>
 
 %<*inv-left-Bool>
 \AgdaTarget{inv-left-B}
 \begin{code}
 inv-left-B : ∀ i → B→n (n→B i) ≡ i
 inv-left-B = λ { False# → refl;  True# → refl;  (Absurd# ()) }
 \end{code}
 %</inv-left-Bool>

 %<*inv-right-Bool>
 \AgdaTarget{inv-right-B}
 \begin{code}
 inv-right-B : ∀ b → n→B (B→n b) ≡ b
 inv-right-B = λ { false → refl;  true → refl }
 \end{code}
 %</inv-right-Bool>


%<*Atomic-Bool>
\AgdaTarget{Atomic-B}
\begin{code}
Atomic-B : Atomic
Atomic-B = record {
      Atom     = B
    ; |Atom|-1 = |B|-1
    ; n→atom   = n→B
    ; atom→n   = B→n
   
    ; inv-left  = inv-left-B
    ; inv-right = inv-right-B
    }
\end{code}
%</Atomic-Bool>
