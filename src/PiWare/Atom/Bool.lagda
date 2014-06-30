\begin{code}
module PiWare.Atom.Bool where

open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Atom using (Atomic)
\end{code}


\begin{code}
private
\end{code}
  \begin{code}
  |𝔹|-1 : ℕ
  |𝔹|-1 = 1
  
  |𝔹| = suc |𝔹|-1
  \end{code}

  %<*pattern-synonyms>
  \begin{code}
  pattern False#    = Fz
  pattern True#     = Fs Fz
  pattern Absurd# n = Fs (Fs n)
  \end{code}
  %</pattern-synonyms>

  %<*nToBool>
  \begin{code}
  n→𝔹 : Fin |𝔹| → 𝔹
  n→𝔹 = λ { False# → false;  True# → true;  (Absurd# ()) }
  \end{code}
  %</nToBool>
  
  %<*boolToN>
  \begin{code}
  𝔹→n : 𝔹 → Fin |𝔹|
  𝔹→n = λ { false → False#;  true → True# }
  \end{code}
  %</boolToN>
  
  %<*inv-left-Bool>
  \begin{code}
  inv-left-𝔹 : ∀ i → 𝔹→n (n→𝔹 i) ≡ i
  inv-left-𝔹 = λ { False# → refl;  True# → refl;  (Absurd# ()) }
  \end{code}
  %</inv-left-Bool>

  %<*inv-right-Bool>
  \begin{code}
  inv-right-𝔹 : ∀ b → n→𝔹 (𝔹→n b) ≡ b
  inv-right-𝔹 = λ { false → refl;  true → refl }
  \end{code}
  %</inv-right-Bool>


%<*Atomic-Bool>
\begin{code}
Atomic-𝔹 : Atomic
Atomic-𝔹 = record {
      Atom     = 𝔹
    ; |Atom|-1 = |𝔹|-1
    ; n→atom   = n→𝔹
    ; atom→n   = 𝔹→n
   
    ; inv-left  = inv-left-𝔹
    ; inv-right = inv-right-𝔹
    }
\end{code}
%</Atomic-Bool>
