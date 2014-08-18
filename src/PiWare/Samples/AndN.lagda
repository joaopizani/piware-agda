\begin{code}
module PiWare.Samples.AndN where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Bool using (false; true; _∧_) renaming (Bool to B)
open import Data.Vec using (Vec; _∷_; replicate; [_]) renaming ([] to ε)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑; ⇓W⇑-Vec)
open import PiWare.Gates.BoolTrio using (BoolTrio; TrueConst#; And#)
open import PiWare.Circuit.Core BoolTrio using (ℂ'; Gate; _⟫'_; _|'_)
open import PiWare.Circuit BoolTrio using (ℂ; Mkℂ; _⟫_; _||_)
open import PiWare.Plugs.Core BoolTrio using (pid')
open import PiWare.Plugs BoolTrio using (pid; pUncons)
open import PiWare.Samples.BoolTrioComb using (∧ℂ)
open import PiWare.Simulation.Core BoolTrio using (⟦_⟧')
open import PiWare.Simulation BoolTrio using (⟦_⟧)
\end{code}


\begin{code}
εℂ' : ℂ' zero 1
εℂ' = Gate TrueConst#

εℂ : {α : Set} {i : ℕ} → ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂ (Vec α zero) B
εℂ ⦃ sα ⦄ = Mkℂ εℂ'
\end{code}

%<*andN-core>
\begin{code}
andN' : ∀ n → ℂ' (n * 1) 1
andN' zero    = εℂ'
andN' (suc n) = pid' {1} |' andN' n  ⟫'  (Gate And#)
\end{code}
%</andN-core>

%<*andN>
\begin{code}
andN : ∀ n → ℂ (Vec B n) B
andN = Mkℂ ∘ andN'
\end{code}
%</andN>

%<*andN-test-4>
\begin{code}
andN-test-4 : ⟦ andN 4 ⟧ (true ∷ true ∷ false ∷ true ∷ ε) ≡ false
andN-test-4 = refl
\end{code}
%</andN-test-4>

%<*proof-andN-core-alltrue>
\begin{code}
proof-andN'-alltrue : ∀ n → ⟦ andN' n ⟧' {{!!}} (replicate true) ≡ [ true ]
proof-andN'-alltrue zero    = refl
proof-andN'-alltrue (suc n) = {!!}
\end{code}
%</proof-andN-core-alltrue>



%<*andNh>
\begin{code}
andNh : ∀ n → ℂ (Vec B n) B
andNh zero    = εℂ
andNh (suc n) = pUncons  ⟫  pid || andNh n  ⟫  ∧ℂ
\end{code}
%</andNh>

%<*andNh-test-4>
\begin{code}
andNh-test-4 : ⟦ andNh 4 ⟧ (true ∷ true ∷ false ∷ true ∷ ε) ≡ false
andNh-test-4 = refl
\end{code}
%</andNh-test-4>


\end{code}

\begin{code}
\end{code}

\begin{code}
postulate undefined : {α : Set} → α
\end{code}

%<*proof-andNh-alltrue>
\begin{code}
proof-andNh-alltrue : ∀ n → ⟦ andNh n ⟧ {undefined} (replicate true) ≡ true
proof-andNh-alltrue zero    = refl
proof-andNh-alltrue (suc n) = {!!}
\end{code}
%</proof-andNh-alltrue>


⟦ pUncons ⟫ (pid || andNh n ⟫ ∧ℂ) ⟧ (true ∷ replicate true)
⟦ pid || andNh n ⟫ ∧ℂ ⟧ (⟦ pUncons ⟧ (true ∷ replicate true))
...
⟦ pid || andNh n ⟫ ∧ℂ ⟧ (true , replicate true)
⟦ ∧ℂ ⟧ (⟦ pid || andNh n ⟧ (true , replicate true))
⟦ ∧ℂ ⟧ (true , ⟦ andNh n ⟧ replicate true)  -- inductive hypothesis
⟦ ∧ℂ ⟧ (true , true)
true
WHAT IS YOUR PROBLEM?!
