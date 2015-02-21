\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs.Core {At : Atomic} (Gt : Gates At) where

open import Function using (id)
open import Data.Nat using (ℕ; suc; _+_; _*_)

open import PiWare.Circuit.Core Gt using (ℂ'X; Plug)
open import PiWare.Plugs.Functions
    using ( swap⤪; ALR⤪; ARL⤪; intertwine⤪; head⤪; vecHalf⤪; vecHalfPow⤪
          ; fst⤪; snd⤪; singleton⤪; forkVec⤪; fork×⤪; uncons⤪; cons⤪)

import Algebra as A
import Data.Nat.Properties as N
open import Algebra.Operations (A.CommutativeSemiring.semiring N.commutativeSemiring) using (_^_)
\end{code}


%<*id-plug-core>
\AgdaTarget{id⤨'}
\begin{code}
id⤨' : ∀ {n} → ℂ'X n n
id⤨' = Plug id
\end{code}
%</id-plug-core>


%<*swap-plug-core>
\AgdaTarget{swap⤨'}
\begin{code}
swap⤨' : ∀ {n m} → ℂ'X (n + m) (m + n)
swap⤨' {n} {m} = Plug (swap⤪ {n} {m})
\end{code}
%</swap-plug-core>


-- associativity plugs
%<*ALR-plug-core>
\AgdaTarget{ALR⤨'}
\begin{code}
ALR⤨' : ∀ {w v y} → ℂ'X ((w + v) + y) (w + (v + y))
ALR⤨' {w} {v} {y} = Plug (ALR⤪ {w} {v} {y})
\end{code}
%</ALR-plug-core>


%<*ARL-plug-core>
\AgdaTarget{ARL⤨'}
\begin{code}
ARL⤨' : ∀ {w v y : ℕ} → ℂ'X (w + (v + y)) ((w + v) + y)
ARL⤨' {w} {v} {y} = Plug (ARL⤪ {w} {v} {y})
\end{code}
%</ARL-plug-core>


%<*intertwine-plug-core>
\AgdaTarget{intertwine⤨'}
\begin{code}
intertwine⤨' : ∀ {a b c d} → ℂ'X ((a + b) + (c + d)) ((a + c) + (b + d))
intertwine⤨' {a} {b} {c} {d} = Plug (intertwine⤪ {a} {b} {c} {d})
\end{code}
%</intertwine-plug-core>


%<*head-plug-core>
\AgdaTarget{head⤨'}
\begin{code}
head⤨' : ∀ {n w} → ℂ'X (suc n * w) w
head⤨' {n} {w} = Plug (head⤪ {n} {w})
\end{code}
%</head-plug-core>


%<*uncons-plug-core>
\AgdaTarget{uncons⤨'}
\begin{code}
uncons⤨' : ∀ {i n} → ℂ'X (suc n * i) (i + n * i)
uncons⤨' {i} {n} = Plug (uncons⤪ {i} {n})
\end{code}
%</uncons-plug-core>


%<*cons-plug-core>
\AgdaTarget{cons⤨'}
\begin{code}
cons⤨' : ∀ {i n} → ℂ'X (i + n * i) (suc n * i)
cons⤨' {i} {n} = Plug (cons⤪ {i} {n})
\end{code}
%</cons-plug-core>


%<*singleton-plug-core>
\AgdaTarget{singleton⤨'}
\begin{code}
singleton⤨' : ∀ {w} → ℂ'X w (1 * w)
singleton⤨' {w} = Plug (singleton⤪ {w})
\end{code}
%</singleton-plug-core>


%<*vecHalf-plug-core>
\AgdaTarget{vecHalf⤨'}
\begin{code}
vecHalf⤨' : ∀ {n w} → ℂ'X ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
vecHalf⤨' {n} {w} = Plug (vecHalf⤪ {n} {w})
\end{code}
%</vecHalf-plug-core>


%<*vecHalfPow-plug-core>
\AgdaTarget{vecHalfPow⤨'}
\begin{code}
vecHalfPow⤨' : ∀ {n w} → ℂ'X ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
vecHalfPow⤨' {n} {w} = Plug (vecHalfPow⤪ {n} {w})
\end{code}
%</vecHalfPow-plug-core>


%<*forkVec-plug-core>
\AgdaTarget{forkVec⤨'}
\begin{code}
forkVec⤨' : ∀ {k n} → ℂ'X n (k * n)
forkVec⤨' {k} {n} = Plug (forkVec⤪ {k} {n})
\end{code}
%</forkVec-plug-core>


%<*forkProd-plug-core>
\AgdaTarget{fork×⤨'}
\begin{code}
fork×⤨' : ∀ {w} → ℂ'X w (w + w)
fork×⤨' {w} = Plug (fork×⤪ {w})
\end{code}
%</forkProd-plug-core>


%<*fst-plug-core>
\AgdaTarget{fst⤨'}
\begin{code}
fst⤨' : ∀ {m n} → ℂ'X (m + n) m
fst⤨' {m} {n} = Plug (fst⤪ {m} {n})
\end{code}
%</fst-plug-core>


%<*snd-plug-core>
\AgdaTarget{snd⤨'}
\begin{code}
snd⤨' : ∀ {m n} → ℂ'X (m + n) n
snd⤨' {m} = Plug (snd⤪ {m})
\end{code}
%</snd-plug-core>
