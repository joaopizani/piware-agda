\begin{code}
module PiWare.ProofSamples.BoolTrioComb where

open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to B)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation BoolTrio using (⟦_⟧)
open import PiWare.Samples.BoolTrioComb using (⊻ℂ; hadd; fadd)
\end{code}


%<*xorEquiv>
\begin{code}
xorEquiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
xorEquiv true  b     = refl
xorEquiv false true  = refl
xorEquiv false false = refl
\end{code}
%</xorEquiv>

%<*proofXor>
\begin{code}
proofXor : ∀ a b → ⟦ ⊻ℂ ⟧ (a , b) ≡ a xor b
proofXor = xorEquiv
\end{code}
%</proofXor>


%<*haddSpec>
\begin{code}
haddSpec : B → B → (B × B)
haddSpec a b = (a ∧ b) , (a xor b)
\end{code}
%</haddSpec>

-- %<*proofHaddBool'>
-- \begin{code}
-- proofHaddBool' : ∀ {a b} → ⟦ hadd ⟧ (a , b) ≡ haddSpec a b
-- proofHaddBool' = proofAnd |≡ proofXor
-- \end{code}
-- %</proofHaddBool'>

-- TODO: better proof here, using proofXor, proofAnd and the "parallel proof combinator"
%<*proofHaddBool>
\begin{code}
proofHaddBool : ∀ a b → ⟦ hadd ⟧ (a , b) ≡ haddSpec a b
proofHaddBool a b = cong (_,_ (a ∧ b)) (xorEquiv a b)
\end{code}
%</proofHaddBool>


-- TODO: make fullAddSpec in terms of halfAddSpec?
%<*faddSpec>
\begin{code}
faddSpec : B → B → B → (B × B)
faddSpec false false false = false , false
faddSpec false false true  = false , true
faddSpec false true  false = false , true
faddSpec false true  true  = true  , false
faddSpec true  false false = false , true
faddSpec true  false true  = true  , false
faddSpec true  true  false = true  , false
faddSpec true  true  true  = true  , true
\end{code}
%</faddSpec>

-- TODO: use eng. proof by reflection to complete the proof "table"
%<*proofFaddBool>
\begin{code}
proofFaddBool : ∀ a b c → ⟦ fadd ⟧ ((a , b) , c) ≡ faddSpec a b c
proofFaddBool true  true  true  = refl
proofFaddBool true  true  false = refl
proofFaddBool true  false true  = refl
proofFaddBool true  false false = refl
proofFaddBool false true  true  = refl
proofFaddBool false true  false = refl
proofFaddBool false false true  = refl
proofFaddBool false false false = refl
\end{code}
%</proofFaddBool>
