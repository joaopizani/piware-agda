\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.AreaAnalysis {At : Atomic} (Gt : Gates At) where

open import Data.Nat.Base using (ℕ; _+_)

open import PiWare.Interface using (Ix)
open import PiWare.Circuit {Gt = Gt} using (ℂ)
open import PiWare.Circuit.Algebra {Gt = Gt} using (ℂσ★; cataℂσ; TyGate★; TyPlug★; Ty⟫★; Ty∥★)
\end{code}


%<*Area>
\AgdaTarget{Area}
\begin{code}
Area : (m n : Ix) → Set
Area _ _ = ℕ
\end{code}
%</Area>


%<*combinator-Area-types>
\begin{code}
gate : TyGate★ Area
plug : TyPlug★ Area
delayLoop : ∀ {i o l} → Area (i + l) (o + l) → Area i o
seq : Ty⟫★ Area
par : Ty∥★ Area
\end{code}
%</combinator-Area-types>

-- TODO: should depend on the gate (spec should be A PARAMETER TYPE)
-- TODO: now we use "1" for the area of the underlying memory element
%<*combinator-Area-defs>
\begin{code}
nil             = 0
gate      _     = 1
plug      _     = 0
delayLoop aᵢ    = 1 + aᵢ
seq       a₁ a₂ = a₁ + a₂
par       a₁ a₂ = a₁ + a₂
\end{code}
%</combinator-Area-defs>


-- TODO: why the need for these implicit parameters being passed here?
%<*area-combinational-algebra>
\AgdaTarget{area-combinational}
\begin{code}
area-combinational : ℂσ★ {Area}
area-combinational = record { Gate★ = gate
                            ; Plug★ = plug
                            ; _⟫★_  = seq {X} {X} {X}
                            ; _∥★_  = par {X} {X} {X} {X}
                            } where postulate X : _
\end{code}
%</area-combinational-algebra>


%<*area-combinational>
\AgdaTarget{⟦\_⟧ₐ}
\begin{code}
⟦_⟧ₐ : ∀ {i o} → ℂ i o → Area i o
⟦_⟧ₐ = cataℂσ area-combinational
\end{code}
%</area-combinational>
