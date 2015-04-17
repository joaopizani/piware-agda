\begin{code}
module PiWare.ProofSamples.BoolTrioComb where

open import Data.Bool.Base using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to B)
open import Data.Product using (_×_; _,_; uncurry′)
open import Data.Vec using (Vec; _∷_) renaming ([] to ε)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Samples.BoolTrioComb.Typed using (⊻ℂ̂; hadd̂; fadd̂)
open import PiWare.Simulation.Typed BoolTrio using (⟦_⟧̂)
\end{code}


%<*xor-spec-table>
\AgdaTarget{⊻ℂ̂-spec-table}
\begin{code}
⊻ℂ̂-spec-table : (B × B) → B
⊻ℂ̂-spec-table (false , false) = false
⊻ℂ̂-spec-table (false , true ) = true
⊻ℂ̂-spec-table (true  , false) = true
⊻ℂ̂-spec-table (true  , true ) = false
\end{code}
%</xor-spec-table>

%<*xor-proof-table>
\AgdaTarget{⊻ℂ̂-proof-table}
\begin{code}
⊻ℂ̂-proof-table : ∀ a b → ⟦ ⊻ℂ̂ ⟧̂ (a , b) ≡ ⊻ℂ̂-spec-table (a , b)
⊻ℂ̂-proof-table false false = refl
⊻ℂ̂-proof-table false true  = refl
⊻ℂ̂-proof-table true  false = refl
⊻ℂ̂-proof-table true  true  = refl
\end{code}
%</xor-proof-table>

%<*xor-spec-subfunc>
\AgdaTarget{⊻ℂ̂-spec-subfunc}
\begin{code}
⊻ℂ̂-spec-subfunc : (B × B) → B
⊻ℂ̂-spec-subfunc = uncurry′ _xor_
\end{code}
%</xor-spec-subfunc>

%<*xor-equiv>
\AgdaTarget{⊻ℂ̂-xor-equiv}
\begin{code}
⊻ℂ̂-xor-equiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
⊻ℂ̂-xor-equiv true  b     = refl
⊻ℂ̂-xor-equiv false true  = refl
⊻ℂ̂-xor-equiv false false = refl
\end{code}
%</xor-equiv>

%<*xor-proof-subfunc>
\AgdaTarget{⊻ℂ̂-proof-subfunc}
\begin{code}
⊻ℂ̂-proof-subfunc : ∀ a b → ⟦ ⊻ℂ̂ ⟧̂ (a , b) ≡ ⊻ℂ̂-spec-subfunc (a , b)
⊻ℂ̂-proof-subfunc = ⊻ℂ̂-xor-equiv
\end{code}
%</xor-proof-subfunc>


%<*haddSpec>
\AgdaTarget{haddSpeĉ}
\begin{code}
haddSpeĉ : B → B → (B × B)
haddSpeĉ a b = (a ∧ b) , (a xor b)
\end{code}
%</haddSpec>

%<*proofHaddBool>
\AgdaTarget{proofHaddBool̂}
\begin{code}
proofHaddBool̂ : ∀ a b → ⟦ hadd̂ ⟧̂ (a , b) ≡ haddSpeĉ a b
proofHaddBool̂ a b = cong (_,_ (a ∧ b)) (⊻ℂ̂-xor-equiv a b)
\end{code}
%</proofHaddBool>

%<*faddSpec>
\AgdaTarget{faddSpeĉ}
\begin{code}
faddSpeĉ : B → B → B → (B × B)
faddSpeĉ false false false = false , false
faddSpeĉ false false true  = false , true
faddSpeĉ false true  false = false , true
faddSpeĉ false true  true  = true  , false
faddSpeĉ true  false false = false , true
faddSpeĉ true  false true  = true  , false
faddSpeĉ true  true  false = true  , false
faddSpeĉ true  true  true  = true  , true
\end{code}
%</faddSpec>

%<*proofFaddBool>
\AgdaTarget{proofFaddBool̂}
\begin{code}
proofFaddBool̂ : ∀ a b c → ⟦ fadd̂ ⟧̂ ((a , b) , c) ≡ faddSpeĉ a b c
proofFaddBool̂ true  true  true  = refl
proofFaddBool̂ true  true  false = refl
proofFaddBool̂ true  false true  = refl
proofFaddBool̂ true  false false = refl
proofFaddBool̂ false true  true  = refl
proofFaddBool̂ false true  false = refl
proofFaddBool̂ false false true  = refl
proofFaddBool̂ false false false = refl
\end{code}
%</proofFaddBool>
