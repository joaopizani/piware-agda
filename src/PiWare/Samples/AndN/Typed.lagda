\begin{code}
module PiWare.Samples.AndN.Typed where

open import Function using (id)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec)

open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit.Typed BoolTrio using (𝐂̂; Mkℂ̂)
open import PiWare.Samples.AndN using (andN)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (⇓W⇑[_,_])
open import PiWare.Synthesizable.Bool using ()
\end{code}



%<*andN-typed>
\AgdaTarget{andN̂}
\begin{code}
andN̂ : ∀ n → 𝐂̂ (Vec B n) B
andN̂ k = Mkℂ̂ ⦃ sα = ⇓W⇑[ id , id ] ⦄ (andN k)
\end{code}
%</andN-typed>
