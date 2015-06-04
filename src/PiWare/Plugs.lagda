\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs {At : Atomic} (Gt : Gates At) where

open import Function using (id)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_)
open import Data.Vec using (allFin)

open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Vec.Extra using (VecNaturalT)
open import Category.NaturalT using (module NaturalT)
open NaturalT using (op)

open import PiWare.Circuit {Gt = Gt} using (𝐂; Plug)
open import PiWare.Plugs.Core
    using ( nil⤪; id⤪; rewireId⤪; swap⤪; ALR⤪; ARL⤪; intertwine⤪; head⤪; vecHalf⤪
          ; vecHalfPow⤪; fst⤪; snd⤪; singleton⤪; forkVec⤪; fork×⤪; uncons⤪; cons⤪)
\end{code}


%<*nil-plug>
\AgdaTarget{nil⤨}
\begin{code}
nil⤨ : ∀ {n} → 𝐂 n 0
nil⤨ = Plug nil⤪
\end{code}
%</nil-plug>


%<*id-plug>
\AgdaTarget{id⤨}
\begin{code}
id⤨ : ∀ {n} → 𝐂 n n
id⤨ = Plug id⤪
\end{code}
%</id-plug>


%<*rewireId-plug>
\AgdaTarget{rewireId⤨}
\begin{code}
rewireId⤨ : ∀ {i o} (p : i ≡ o) → 𝐂 i o
rewireId⤨ p = Plug (rewireId⤪ p)
\end{code}
%</rewireId-plug>


%<*swap-plug>
\AgdaTarget{swap⤨}
\begin{code}
swap⤨ : ∀ {n m} → 𝐂 (n + m) (m + n)
swap⤨ {n} {m} = Plug (swap⤪ {n} {m})
\end{code}
%</swap-plug>


-- associativity plugs
%<*ALR-plug>
\AgdaTarget{ALR⤨}
\begin{code}
ALR⤨ : ∀ {w v y} → 𝐂 ((w + v) + y) (w + (v + y))
ALR⤨ {w} {v} {y} = Plug (ALR⤪ {w} {v} {y})
\end{code}
%</ALR-plug>


%<*ARL-plug>
\AgdaTarget{ARL⤨}
\begin{code}
ARL⤨ : ∀ {w v y : ℕ} → 𝐂 (w + (v + y)) ((w + v) + y)
ARL⤨ {w} {v} {y} = Plug (ARL⤪ {w} {v} {y})
\end{code}
%</ARL-plug>


%<*intertwine-plug>
\AgdaTarget{intertwine⤨}
\begin{code}
intertwine⤨ : ∀ {a b c d} → 𝐂 ((a + b) + (c + d)) ((a + c) + (b + d))
intertwine⤨ {a} {b} {c} {d} = Plug (intertwine⤪ {a} {b} {c} {d})
\end{code}
%</intertwine-plug>


%<*head-plug>
\AgdaTarget{head⤨}
\begin{code}
head⤨ : ∀ {n w} → 𝐂 (suc n * w) w
head⤨ {n} {w} = Plug (head⤪ {n} {w})
\end{code}
%</head-plug>


%<*uncons-plug>
\AgdaTarget{uncons⤨}
\begin{code}
uncons⤨ : ∀ {i n} → 𝐂 (suc n * i) (i + n * i)
uncons⤨ {i} {n} = Plug (uncons⤪ {i} {n})
\end{code}
%</uncons-plug>


%<*cons-plug>
\AgdaTarget{cons⤨}
\begin{code}
cons⤨ : ∀ {i n} → 𝐂 (i + n * i) (suc n * i)
cons⤨ {i} {n} = Plug (cons⤪ {i} {n})
\end{code}
%</cons-plug>


%<*singleton-plug>
\AgdaTarget{singleton⤨}
\begin{code}
singleton⤨ : ∀ {w} → 𝐂 w (1 * w)
singleton⤨ {w} = Plug (singleton⤪ {w})
\end{code}
%</singleton-plug>


%<*vecHalf-plug>
\AgdaTarget{vecHalf⤨}
\begin{code}
vecHalf⤨ : ∀ {n w} → 𝐂 ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
vecHalf⤨ {n} {w} = Plug (vecHalf⤪ {n} {w})
\end{code}
%</vecHalf-plug>


%<*vecHalfPow-plug>
\AgdaTarget{vecHalfPow⤨}
\begin{code}
vecHalfPow⤨ : ∀ {n w} → 𝐂 ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
vecHalfPow⤨ {n} {w} = Plug (vecHalfPow⤪ {n} {w})
\end{code}
%</vecHalfPow-plug>


%<*forkVec-plug>
\AgdaTarget{forkVec⤨}
\begin{code}
forkVec⤨ : ∀ {k n} → 𝐂 n (k * n)
forkVec⤨ {k} {n} = Plug (forkVec⤪ {k} {n})
\end{code}
%</forkVec-plug>


%<*forkProd-plug>
\AgdaTarget{fork×⤨}
\begin{code}
fork×⤨ : ∀ {w} → 𝐂 w (w + w)
fork×⤨ {w} = Plug (fork×⤪ {w})
\end{code}
%</forkProd-plug>


%<*fst-plug>
\AgdaTarget{fst⤨}
\begin{code}
fst⤨ : ∀ {m n} → 𝐂 (m + n) m
fst⤨ {m} {n} = Plug (fst⤪ {m} {n})
\end{code}
%</fst-plug>


%<*snd-plug>
\AgdaTarget{snd⤨}
\begin{code}
snd⤨ : ∀ {m n} → 𝐂 (m + n) n
snd⤨ {m} = Plug (snd⤪ {m})
\end{code}
%</snd-plug>


%<*plug-Vec-eta>
\AgdaTarget{plug-Vecη}
\begin{code}
plug-Vecη : ∀ {i o} → VecNaturalT i o → 𝐂 i o
plug-Vecη η = Plug (op η (allFin _))
\end{code}
%</plug-Vec-eta>
