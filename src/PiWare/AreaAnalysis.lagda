\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.AreaAnalysis {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _+_)

open import PiWare.Interface using (Ix)
open import PiWare.Circuit Gt using (ℂ)
open import PiWare.Circuit.Algebra Gt using (ℂσ★; cataℂσ; TyGate★; TyPlug★; Ty⟫★; Ty∥★; Ty⑆★)
\end{code}

\begin{code}
Area : (m n : Ix) → Set
Area _ _ = ℕ

gate : TyGate★ Area
plug : TyPlug★ Area
delayLoop : ∀ {i o l} → Area (i + l) (o + l) → Area i o
seq : Ty⟫★ Area
par : Ty∥★ Area
sum : Ty⑆★ Area

nil = 0
gate _ = 1  -- TODO: should depend on the gate (spec should be A PARAMETER TYPE)
plug _ = 0
delayLoop aᵢ = 1 + aᵢ  --TODO: now we use "1" for the area of the underlying memory element
seq a₁ a₂ = a₁ + a₂
par a₁ a₂ = a₁ + a₂
sum a₁ a₂ = 1 + (a₁ + a₂)  --TODO: now we use "1" for the area of the underlying mux

area-combinational★ : ℂσ★ {Area}
area-combinational★ = record
  { Gate★ = gate;                Plug★ = plug
  ; _⟫★_ = seq {X} {X} {X};  _∥★_ = par {X} {X} {X} {X};  _⑆★_ = sum {X} {X} {X}
  } where postulate X : _

⟦_⟧ₐ : ∀ {i o} → ℂ i o → Area i o
⟦_⟧ₐ = cataℂσ area-combinational★
\end{code}
