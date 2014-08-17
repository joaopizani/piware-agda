\begin{code}
module PiWare.ProofSamples.BoolTrioComb where

open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to B)
open import Data.Product using (_×_; _,_; uncurry′)
open import Data.Vec using (Vec; _∷_) renaming ([] to ε)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation BoolTrio using (⟦_⟧)
open import PiWare.Samples.BoolTrioComb using (⊻ℂ; hadd; fadd)
\end{code}


%<*xor-spec-table>
\begin{code}
⊻ℂ-spec-table : (B × B) → B
⊻ℂ-spec-table  (false  ,  false)  = false
⊻ℂ-spec-table  (false  ,  true )  = true
⊻ℂ-spec-table  (true   ,  false)  = true
⊻ℂ-spec-table  (true   ,  true )  = false
\end{code}
%</xor-spec-table>

%<*xor-proof-table>
\begin{code}
⊻ℂ-proof-table : ∀ a b → ⟦ ⊻ℂ ⟧ (a , b) ≡ ⊻ℂ-spec-table (a , b)
⊻ℂ-proof-table  false  false  = refl
⊻ℂ-proof-table  false  true   = refl
⊻ℂ-proof-table  true   false  = refl
⊻ℂ-proof-table  true   true   = refl
\end{code}
%</xor-proof-table>

%<*xor-spec-subfunc>
\begin{code}
⊻ℂ-spec-subfunc : (B × B) → B
⊻ℂ-spec-subfunc = uncurry′ _xor_
\end{code}
%</xor-spec-subfunc>

%<*xor-equiv-decl>
\begin{code}
⊻ℂ-xor-equiv : ∀ a b → (not a ∧ b) ∨ (a ∧ not b) ≡ (a xor b)
\end{code}
%</xor-equiv-decl>
%<*xor-equiv-def>
\begin{code}
⊻ℂ-xor-equiv true  b     = refl
⊻ℂ-xor-equiv false true  = refl
⊻ℂ-xor-equiv false false = refl
\end{code}
%</xor-equiv-def>

%<*xor-proof-subfunc>
\begin{code}
⊻ℂ-proof-subfunc : ∀ a b → ⟦ ⊻ℂ ⟧ (a , b) ≡ ⊻ℂ-spec-subfunc (a , b)
⊻ℂ-proof-subfunc = ⊻ℂ-xor-equiv
\end{code}
%</xor-proof-subfunc>


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
proofHaddBool a b = cong (_,_ (a ∧ b)) (⊻ℂ-xor-equiv a b)
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
