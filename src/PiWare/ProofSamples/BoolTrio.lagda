\begin{code}
module PiWare.ProofSamples.BoolTrio where

open import Function using (_$_; _∘_)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to ε; _∷_ to _◁_)
open import Data.Product using (_×_; _,_) renaming (map to mapₚ)
open import Data.Bool using (not; _∧_; _∨_; _xor_; true; false) renaming (Bool to B)

open import Data.Stream using (Stream; repeat; _≈_; zipWith; _∷_; take; head; tail; iterate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Coinduction using (♯_; ♭)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation BoolTrio using (⟦_⟧; ⟦_⟧*)

open import PiWare.Samples.BoolTrio
     using (¬ℂ; ∧ℂ; ∨ℂ; ⊻ℂ; ¬∧ℂ; hadd; fadd; shift; toggle; reg)
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


%<*toggle7>
\begin{code}
toggle7 = take 7 $ ⟦ toggle ⟧* (repeat tt)
\end{code}
%</toggle7>

%<*shift7>
\begin{code}
shift7 = take 7 $ ⟦ shift ⟧* (iterate not false)
\end{code}
%</shift7>

%<*rhold>
\begin{code}
rhold = take 7 (⟦ reg ⟧* $
                  zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false))
                              (true ∷ ♯ repeat false))
\end{code}
%</rhold>

%<*rload>
\begin{code}
rload = take 7 (⟦ reg ⟧* $
                  zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false))
                              (false ∷ ♯ (true ∷ ♯ repeat false)) )
\end{code}
%</rload>



%<*proofShiftHead>
\begin{code}
proofShiftHead : ∀ {x y zs} → head (⟦ shift ⟧* (x ∷ ♯ (y ∷ ♯ zs)) ) ≡ false
proofShiftHead = refl
\end{code}
%</proofShiftHead>

%<*proofShiftTail>
\begin{code}
proofShiftTail : ∀ {ins} → tail (⟦ shift ⟧* ins) ≈ ins
proofShiftTail = {!!}
\end{code}
%</proofShiftTail>


-- \begin{code}
-- proofToggle  : ⟦ toggle ⟧* (repeat tt) ≈ iterate not true
-- proofToggle = refl ∷ ♯ {!!}
-- \end{code}
 
-- now with the register: first the tail
-- %<*proofRegNeverLoadHardcoded'>
-- \begin{code}
-- proofRegNeverLoadHardcoded' : tail (⟦ reg ⟧* (repeat (true , false))) ≈ repeat false
-- proofRegNeverLoadHardcoded' = refl ∷ ♯ proofRegNeverLoadHardcoded'
-- \end{code}
-- %</proofRegNeverLoadHardcoded'>

-- -- then the case including the head
-- %<*proofRegNeverLoadHardcoded>
-- \begin{code}
-- proofRegNeverLoadHardcoded : ⟦ reg ⟧* (repeat (true , false)) ≈ false ∷ ♯ repeat false
-- proofRegNeverLoadHardcoded = refl ∷ ♯ proofRegNeverLoadHardcoded'
-- \end{code}
-- %</proofRegNeverLoadHardcoded>

-- -- trying to be a bit more general now: first the tail
-- %<*proofRegNeverLoad'>
-- \begin{code}
-- proofRegNeverLoad' : ∀ xs → tail (⟦ reg ⟧* $ zipWith _,_ xs (repeat false) ) ≈ repeat false
-- proofRegNeverLoad' (x ∷ xs) = refl ∷ ♯ proofRegNeverLoad' (♭ xs)
-- \end{code}
-- %</proofRegNeverLoad'>

-- -- then the case including the head...
-- %<*proofRegNeverLoad>
-- \begin{code}
-- proofRegNeverLoad : ∀ xs → ⟦ reg ⟧* (zipWith _,_ xs (repeat false)) ≈ false ∷ ♯ repeat false
-- proofRegNeverLoad xs = refl ∷ ♯ proofRegNeverLoad' xs
-- \end{code}
-- %</proofRegNeverLoad>


-- -- when load, tail of output is input
-- -- first hardcoded
-- %<*proofRegAlwaysLoadHardcoded'>
-- \begin{code}
-- proofRegAlwaysLoadHardcoded' : tail (⟦ reg ⟧* (repeat (true , true))) ≈ repeat true
-- proofRegAlwaysLoadHardcoded' = refl ∷ ♯ proofRegAlwaysLoadHardcoded'
-- \end{code}
-- %</proofRegAlwaysLoadHardcoded'>

-- %<*proofRegAlwaysLoadHardcoded>
-- \begin{code}
-- proofRegAlwaysLoadHardcoded : ⟦ reg ⟧* (repeat (true , true)) ≈ false ∷ ♯ repeat true
-- proofRegAlwaysLoadHardcoded = refl ∷ ♯ proofRegAlwaysLoadHardcoded'
-- \end{code}
-- %</proofRegAlwaysLoadHardcoded>

-- %<*proofRegAlwaysLoad'>
-- \begin{code}
-- proofRegAlwaysLoad' : ∀ xs → tail (⟦ reg ⟧* (zipWith _,_ xs (repeat true))) ≈ xs
-- proofRegAlwaysLoad' (true  ∷ xs) = refl ∷ ♯ {!proofRegAlwaysLoad' (♭ xs)!}
-- proofRegAlwaysLoad' (false ∷ xs) = refl ∷ ♯ proofRegAlwaysLoad' (♭ xs)  -- "coincidence"?
-- \end{code}
-- %</proofRegAlwaysLoad'>

-- %<*proofRegAlwaysLoad>
-- \begin{code}
-- proofRegAlwaysLoad : ∀ xs → ⟦ reg ⟧* (zipWith _,_ xs (repeat true)) ≈ false ∷ ♯ xs
-- proofRegAlwaysLoad xs = refl ∷ ♯ proofRegAlwaysLoad' xs
-- \end{code}
-- %</proofRegAlwaysLoad>
