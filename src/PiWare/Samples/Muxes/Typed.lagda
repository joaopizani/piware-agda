\begin{code}
module PiWare.Samples.Muxes.Typed where

open import Data.Nat.Base using (_+_; _*_)
open import Data.Bool.Base using () renaming (Bool to B)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; proj₂)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Typed BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.Muxes using (mux; muxN)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable.Bool using ()
open import PiWare.Synthesizable Atomic-B using (⇓W⇑)

open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open CommutativeSemiring ℕ-commSemiring using (*-identity)
*-identityᵣ = proj₂ *-identity
\end{code}


%<*mux-typed>
\AgdaTarget{mux̂}
\begin{code}
mux̂ : 𝐂̂ (B × (B × B)) B
mux̂ = Mkℂ̂ mux
\end{code}
%</mux-typed>


\begin{code}
postulate muxN̂-sα : ∀ n → ⇓W⇑ (B × (Vec B n × Vec B n)) {1 + (n + n)}
postulate muxN̂-sβ : ∀ n → ⇓W⇑ (Vec B n) {n}
\end{code}

%<*muxN-typed>
\AgdaTarget{muxN}
\begin{code}
muxN̂ : ∀ n → 𝐂̂ (B × (Vec B n × Vec B n)) (Vec B n) {1 + ((n * 1) + (n * 1))} {n * 1}
muxN̂ n rewrite *-identityᵣ n = Mkℂ̂ ⦃ muxN̂-sα n ⦄ ⦃ muxN̂-sβ n ⦄ (muxN n)
\end{code}
%</muxN-typed>
