\begin{code}
module PiWare.Atom.Bool where

open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat using (s≤s; z≤n)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Atom using (AtomInfo)
\end{code}


\begin{code}
private
\end{code}
  %<*nToBool>
  \begin{code}
  n→𝔹 : Fin 2 → 𝔹
  n→𝔹 Fz = false
  n→𝔹 (Fs Fz) = true
  n→𝔹 (Fs (Fs ()))
  \end{code}
  %</nToBool>
  
  %<*boolToN>
  \begin{code}
  𝔹→n : 𝔹 → Fin 2
  𝔹→n false = Fz
  𝔹→n true  = Fs Fz
  \end{code}
  %</boolToN>
  
  
  %<*inv-left-bool>
  \begin{code}
  inv-left-𝔹 : ∀ i → 𝔹→n (n→𝔹 i) ≡ i
  inv-left-𝔹 Fz = refl
  inv-left-𝔹 (Fs Fz) = refl
  inv-left-𝔹 (Fs (Fs ()))
  \end{code}
  %</inv-left-bool>

  %<*inv-right-bool>
  \begin{code}
  inv-right-𝔹 : ∀ b → n→𝔹 (𝔹→n b) ≡ b
  inv-right-𝔹 false = refl
  inv-right-𝔹 true  = refl
  \end{code}
  %</inv-right-bool>


%<*AtomBool>
\begin{code}
Atom𝔹 : AtomInfo
Atom𝔹 = record {
      Atom = 𝔹
    ; card = 2
    ; n→atom = n→𝔹
    ; atom→n = 𝔹→n
   
    ; card≥2 = s≤s (s≤s z≤n)
    ; inv-left  = inv-left-𝔹
    ; inv-right = inv-right-𝔹
    }
\end{code}
%</AtomBool>
