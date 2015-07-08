\begin{code}
module PiWare.Circuit.Applicative where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool.Base using (Bool)
open import Data.Vec using (Vec)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Atom using (module Atomic)
open Atomic Atomic-B using (W)
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Circuit {Gt = BoolTrio} using (𝐂; _∥_; _⟫_)
open import PiWare.Plugs BoolTrio using (id⤨)
open import PiWare.Samples.BoolTrioComb using (∧ℂ; ¬ℂ)
\end{code}


\begin{code}
infixl 0 _﹩_

_﹩_ : ∀ {a b m n} → 𝐂 (a + n) b → 𝐂 m a → 𝐂 (m + n) b
_﹩_ c cₐ = cₐ ∥ id⤨ ⟫ c

test₁ : 𝐂 2 1
test₁ = ∧ℂ ﹩ ¬ℂ ﹩ ¬ℂ
\end{code}
