\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)

module PiWare.Circuit.Semigroup {At : Atomic} where

open import Function using (const)
open import Data.Fin using () renaming (zero to Fz)
open import Data.Vec using ([]; _∷_; [_])
open import Algebra.Structures using (IsSemigroup)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Atomic At using (Atom)
open import PiWare.Gates At using (Gates; W⟶W)
open import PiWare.Circuit {At} using (𝐂; _⟫_; _∥_; Gate)
open import PiWare.Plugs {At} using (id⤨)
open import PiWare.Simulation.Equality {At} using (_≋_)
\end{code}


%<*Circuit-binary>
\AgdaTarget{𝐂₂}
\begin{code}
𝐂₂ : {Gt : Gates} → Set
𝐂₂ {Gt} = 𝐂 {Gt} 2 1
\end{code}
%</Circuit-binary>


%<*IsAssoc-Circuit-binary>
\AgdaTarget{IsAssoc-𝐂₂}
\begin{code}
IsAssoc𝐂₂ : {Gt : Gates} → 𝐂₂ {Gt} → Set
IsAssoc𝐂₂ {Gt} ⊕𝐂 = (⊕𝐂 ∥ id⤨₁ ⟫ ⊕𝐂) ≋′ (id⤨₁ ∥ ⊕𝐂 ⟫ ⊕𝐂)
  where  id⤨₁  = id⤨ Gt {1}
         _≋′_   = _≋_ Gt
\end{code}
%</IsAssoc-Circuit-binary>


%<*Semigroup-Circuit-binary>
\AgdaTarget{Semigroup-𝐂₂}
\begin{code}
record Semigroup𝐂₂ {Gt : Gates} : Set where
  field
    ⊕𝐂       : 𝐂₂ {Gt}
    isAssoc  : IsAssoc𝐂₂ ⊕𝐂
\end{code}
%</Semigroup-Circuit-binary>


\begin{code}
private W₂⟶W₁ = W⟶W 2 1
\end{code}

%<*binOp-to-Spec>
\AgdaTarget{Op₂⟶Spec}
\begin{code}
Op₂⟶Spec : Op₂ Atom → W₂⟶W₁
Op₂⟶Spec _·_ (x ∷ y ∷ []) = [ x · y ]
\end{code}
%</binOp-to-Spec>

%<*Op2-to-Gates>
\AgdaTarget{·Gt}
\begin{code}
Op₂⟶Gates : Op₂ Atom → Gates
Op₂⟶Gates _·_ = record { |Gates| = 1;  |in| = const 2;  |out| = const 1;  spec = const (Op₂⟶Spec _·_) }
\end{code}
%</Op2-to-Gates>

%<*Op2-to-Semigroup-Circuit-binary>
\AgdaTarget{gate-Semigroup-𝐂₂}
\begin{code}
Op₂⟶Semigroup𝐂₂ : (op : Op₂ Atom) ⦃ sg : IsSemigroup (_≡_ {A = Atom}) op ⦄ → Semigroup𝐂₂ {Op₂⟶Gates op}
Op₂⟶Semigroup𝐂₂ op ⦃ sg ⦄ =  record { ⊕𝐂 = Gate {Op₂⟶Gates op} Fz; isAssoc = isAssoc-·𝐂 }
  where postulate isAssoc-·𝐂 : _
\end{code}
%</Op2-to-Semigroup-Circuit-binary>
