\begin{code}
module PiWare.ProofSamples.BoolTrioSeq where

open import Function using (_$_)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; not; false; true)
open import Data.Product using (_,_)
open import Data.Vec using (replicate) renaming (_∷_ to _◁_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Coinduction using (♯_; ♭)
open import Data.Stream using (Stream; _∷_; head; tail; take; repeat; iterate; zipWith; _≈_)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Simulation BoolTrio using (⟦_⟧*)
open import PiWare.Samples.BoolTrioSeq using (toggle; shift; reg)
\end{code}


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

%<*load2>
\begin{code}
loads inputs : Stream Bool
loads   = true ∷ ♯ (true  ∷ ♯ (false ∷ ♯ repeat false))
inputs  = true ∷ ♯ (false ∷ ♯ (true  ∷ ♯ repeat false))

load2 = take 7 (⟦ reg ⟧* $ zipWith _,_ inputs loads) ≡ true ◁ replicate false
\end{code}
%</load2>

%<*rload>
\begin{code}
rload = take 7 (⟦ reg ⟧* $
                  zipWith _,_ (true ∷ ♯ (true ∷ ♯ repeat false))
                              (false ∷ ♯ (true ∷ ♯ repeat false)) )
\end{code}
%</rload>



-- %<*proofShiftHead>
-- \begin{code}
-- proofShiftHead : ∀ {x y zs} → head (⟦ shift ⟧* (x ∷ ♯ (y ∷ ♯ zs)) ) ≡ false
-- proofShiftHead = refl
-- \end{code}
-- %</proofShiftHead>

-- %<*proofShiftTail>
-- \begin{code}
-- proofShiftTail : ∀ {ins} → tail (⟦ shift ⟧* ins) ≈ ins
-- proofShiftTail {true ∷ xs} = {!!}
-- proofShiftTail {false ∷ xs} = {!!}
-- \end{code}
-- %</proofShiftTail>


-- \begin{code}
-- proofToggle  : ⟦ toggle ⟧* (repeat tt) ≈ iterate not true
-- proofToggle = refl ∷ ♯ {!!}
-- \end{code}
 

-- when load, tail of output is input
-- first hardcoded
-- %<*proofRegAlwaysLoadHardcoded'>
-- \begin{code}
-- proofRegAlwaysLoadHardcoded' : tail (⟦ reg ⟧* (repeat (true , true))) ≈ repeat true
-- proofRegAlwaysLoadHardcoded' = refl ∷ ♯ ?
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
