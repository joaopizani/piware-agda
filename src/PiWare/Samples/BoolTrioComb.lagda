\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import PiWare.Atom.Bool using (Atomic-B; False#; True#)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio; ⊥ℂ#; ⊤ℂ#; ¬ℂ#; ∧ℂ#; ∨ℂ#)
open import PiWare.Plugs BoolTrio using (fork×⤨; id⤨; ALR⤨; ARL⤨)
open import PiWare.Circuit BoolTrio using (ℂX; Mkℂ; _⟫_; _||_; |+; gateℂ)
\end{code}


%<*fundamentals>
\AgdaTarget{⊥ℂ, ⊤ℂ, ¬ℂ, ∧ℂ, ∨ℂ}
\begin{code}
⊥ℂ ⊤ℂ : ℂX ⊤ B
⊥ℂ = gateℂ ⊥ℂ#
⊤ℂ = gateℂ ⊤ℂ#

¬ℂ : ℂX B B
¬ℂ = gateℂ ¬ℂ#

∧ℂ ∨ℂ : ℂX (B × B) B
∧ℂ = gateℂ ∧ℂ#
∨ℂ = gateℂ ∨ℂ#
\end{code}
%</fundamentals>

%<*nand>
\AgdaTarget{¬∧ℂ}
\begin{code}
¬∧ℂ : ℂX (B × B) B
¬∧ℂ = ∧ℂ ⟫ ¬ℂ
\end{code}
%</nand>

%<*xor>
\AgdaTarget{⊻ℂ}
\begin{code}
⊻ℂ : ℂX (B × B) B
⊻ℂ =   fork×⤨
     ⟫ (¬ℂ || id⤨ ⟫ ∧ℂ)  ||  (id⤨ || ¬ℂ ⟫ ∧ℂ)
     ⟫                   ∨ℂ
\end{code}
%</xor>


a × b → c × s
%<*hadd>
\AgdaTarget{hadd}
\begin{code}
hadd : ℂX (B × B) (B × B)
hadd =    fork×⤨
       ⟫ ∧ℂ || ⊻ℂ
\end{code}
%</hadd>


(a × b) × cin → co × s
%<*fadd>
\AgdaTarget{fadd}
\begin{code}
fadd : ℂX ((B × B) × B) (B × B)
fadd =   hadd ||  id⤨
       ⟫     ALR⤨
       ⟫ id⤨  || hadd
       ⟫    ARL⤨
       ⟫  ∨ℂ  ||  id⤨
\end{code}
%</fadd>
