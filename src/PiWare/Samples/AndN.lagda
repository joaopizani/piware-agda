\begin{code}
module PiWare.Samples.AndN where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (false; true; _∧_) renaming (Bool to B)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; _∷_; replicate; [_]) renaming ([] to ε)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import PiWare.Utils using (splitAt')
open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑; ⇓W⇑-Vec)
open import PiWare.Gates.BoolTrio using (BoolTrio; TrueConst#; And#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _|'_; _⟫'_)
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; _⟫_; _||_)
open import PiWare.Plugs.Core BoolTrio using (pid')
open import PiWare.Plugs BoolTrio using (pid; pUncons)
open import PiWare.Samples.BoolTrioComb using (∧ℂ)
open import PiWare.Simulation.Core BoolTrio using (⟦_⟧')
open import PiWare.Simulation BoolTrio using (⟦_⟧)
\end{code}


\begin{code}
εℂ : {α : Set} {i : ℕ} → ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂ (Vec α zero) B
εℂ ⦃ sα ⦄ = Mkℂ (Gate TrueConst#)
\end{code}

%<*andN>
\begin{code}
andN : ∀ n → ℂ (Vec B n) B
andN zero    = εℂ
andN (suc n) = pUncons  ⟫  pid || andN n  ⟫  ∧ℂ
\end{code}
%</andN>

%<*andN-test-4>
\begin{code}
andN-test-4 : ⟦ andN 4 ⟧ (true ∷ true ∷ false ∷ true ∷ ε) ≡ false
andN-test-4 = refl
\end{code}
%</andN-test-4>


\begin{code}
postulate undefined : {α : Set} → α
\end{code}

%<*proof-andN-alltrue>
\begin{code}
proof-andN-alltrue : ∀ n → ⟦ andN n ⟧ {undefined} (replicate true) ≡ true
proof-andN-alltrue zero    = refl
proof-andN-alltrue (suc n) = {!!}
\end{code}
%</proof-andN-alltrue>


-- assuming _⟫_ is left-associative
⟦ pUncons ⟫ pid || andN n ⟫ ∧ℂ ⟧ (true ∷ replicate true)
⟦ (pUncons ⟫ pid || andN n) ⟫ ∧ℂ) ⟧ (true ∷ replicate true)
⟦ ∧ℂ ⟧ (⟦ pUncons ⟫ pid || andN n ⟧ (true ∷ replicate true))
⟦ ∧ℂ ⟧ (⟦ pid || andN n ⟧ (⟦ pUncons ⟧ (true ∷ replicate true)))
⟦ ∧ℂ ⟧ (⟦ pid || andN n ⟧ (true , replicate true))
⟦ ∧ℂ ⟧ (map ⟦ pid ⟧ ⟦ andN n ⟧ (true , replicate true))
⟦ ∧ℂ ⟧ (⟦ pid ⟧ true , ⟦ andN n ⟧ replicate true)
⟦ ∧ℂ ⟧ (true , ⟦ andN n ⟧ replicate true)  -- induction hypothesis
⟦ ∧ℂ ⟧ (true , true)
true ∧ true
true



-- assuming _⟫_ is right-associative
⟦ pUncons ⟫ pid || andN n ⟫ ∧ℂ ⟧ (true ∷ replicate true)
⟦ pUncons ⟫ (pid || andN n ⟫ ∧ℂ) ⟧ (true ∷ replicate true)
⟦ pid || andN n ⟫ ∧ℂ ⟧ (⟦ pUncons ⟧ (true ∷ replicate true))
⟦ pid || andN n ⟫ ∧ℂ ⟧ (true , replicate true)
⟦ ∧ℂ ⟧ (⟦ pid || andN n ⟧ (true , replicate true))
⟦ ∧ℂ ⟧ (true , ⟦ andN n ⟧ replicate true)  -- inductive hypothesis
⟦ ∧ℂ ⟧ (true , true)
true
WHAT IS YOUR PROBLEM?!


<*andN-core>
\begin{code}
andN' : ∀ n → ℂ' n 1
andN' zero    = Gate TrueConst#
andN' (suc n) = pid' {1} |' andN' n  ⟫'  Gate And#
\end{code}
</andN-core>

<*proof-andN-core-alltrue>
\begin{code}
proof-andN-core-alltrue : ∀ n → ⟦ andN' n ⟧' {undefined} (replicate true) ≡ [ true ]
proof-andN-core-alltrue zero    = refl
proof-andN-core-alltrue (suc n) = {!!}
\end{code}
</proof-andN-core-alltrue>



%<*pidN>
--\begin{code}
pidN : ∀ n → ℂ B B
pidN zero    = pid
pidN (suc n) = pid ⟫ pidN n
--\end{code}
%</pidN>

%<*proof-idN>
--\begin{code}
proof-pidN : (n : ℕ) (b : B) → ⟦ pidN n ⟧ {undefined} b ≡ b
proof-pidN zero    b = refl
proof-pidN (suc n) b = {!!}
--\end{code}
%</proof-idN>
