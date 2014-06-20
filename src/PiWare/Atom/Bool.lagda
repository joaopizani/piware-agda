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

  \begin{code}
  pattern F0 = Fz
  pattern F1 = Fs F0
  pattern F2 n = Fs (Fs n)
  \end{code}

  %<*nToBool>
  \begin{code}
  n→𝔹 : Fin |𝔹| → 𝔹
  n→𝔹 = λ { F0 → false;  F1 → true;  (F2 ()) }
  \end{code}
  %</nToBool>
  
  %<*boolToN>
  \begin{code}
  𝔹→n : 𝔹 → Fin |𝔹|
  𝔹→n = λ { false → F0;  true → F1 }
  \end{code}
  %</boolToN>
  
  %<*inv-left-bool>
  \begin{code}
  inv-left-𝔹 : ∀ i → 𝔹→n (n→𝔹 i) ≡ i
  inv-left-𝔹 = λ { F0 → refl;  F1 → refl;  (F2 ()) }
  \end{code}
  %</inv-left-bool>

  %<*inv-right-bool>
  \begin{code}
  inv-right-𝔹 : ∀ b → n→𝔹 (𝔹→n b) ≡ b
  inv-right-𝔹 = λ { false → refl;  true → refl }
  \end{code}
  %</inv-right-bool>


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
