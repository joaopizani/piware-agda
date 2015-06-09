\begin{code}
module PiWare.Plugs.Core where

open import Function using (id; _$_; flip)
open import Data.Fin using (Fin; inject+; raise)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; map; _++_; lookup; tabulate; splitAt; replicate; concat) renaming ([] to ε; _∷_ to _◁_)
open import Data.Nat.Base using (zero; suc; _+_; _*_)

open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; refl; _≡_; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_)

open import Data.Nat.Properties.Simple using (*-right-zero; +-right-identity)
open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring; module SemiringSolver to ℕ-SemiringSolver)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm; *-assoc; *-comm; distribʳ-*-+)
open import Algebra.Operations (CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)
open ℕ-SemiringSolver using (solve; _:=_; con; _:+_; _:*_)

open import PiWare.Interface using (Ix)
\end{code}


\begin{code}
infix 8 _⤪_
\end{code}

%<*Plug-type>
\AgdaTarget{\_⤪\_}
\begin{code}
_⤪_ : Ix → Ix → Set
i ⤪ o = Vec (Fin i) o
\end{code}

%</Plug-type>


%<*Plug-par>
\AgdaTarget{\_|⤪\_}
\begin{code}
infixr 7 _|⤪_

_|⤪_ : ∀ {a b c d} → a ⤪ b → c ⤪ d → (a + c) ⤪ (b + d)
_|⤪_ {a} {b} {c} {d} f g = map (inject+ c) f ++ map (raise a) g
\end{code}
%</Plug-par>

%<*Plug-seq>
\AgdaTarget{\_⟫⤪\_}
\begin{code}
infixr 6 _⟫⤪_

_⟫⤪_ : ∀ {a b c} → a ⤪ b → b ⤪ c → a ⤪ c
f ⟫⤪ g = map (flip lookup f) g
\end{code}
%<*Plug-seq>


%<*nil-fin>
\AgdaTarget{nil⤪}
\begin{code}
nil⤪ : ∀ {n} → n ⤪ 0
nil⤪ = ε
\end{code}
%</nil-fin>


%<*id-fin>
\AgdaTarget{id⤪}
\begin{code}
id⤪ : ∀ {n} → n ⤪ n
id⤪ = tabulate id
\end{code}
%</id-fin>


%<*adaptId-fin>
\AgdaTarget{adaptId⤪}
\begin{code}
adaptId⤪ : ∀ {n n′} (p : n ≡ n′) → n ⤪ n′
adaptId⤪ refl = id⤪
\end{code}
%</adaptId-fin>


%<*swap-fin>
\AgdaTarget{swap⤪}
\begin{code}
swap⤪ : ∀ {n m} → (n + m) ⤪ (m + n)
swap⤪ {n} {m} with splitAt n (tabulate id)
swap⤪ {n} {m} | vₙ , vₘ , _ = vₘ ++ vₙ
\end{code}
%</swap-fin>


%<*ALR-fin>
\AgdaTarget{ALR⤪}
\begin{code}
ALR⤪ : ∀ {w v y} → ((w + v) + y) ⤪ (w + (v + y))
ALR⤪ {w} {v} {y} = adaptId⤪ (+-assoc w v y)
\end{code}
%</ALR-fin>


%<*ARL-fin>
\AgdaTarget{ARL⤪}
\begin{code}
ARL⤪ : ∀ {w v y} → (w + (v + y)) ⤪ ((w + v) + y)
ARL⤪ {w} {v} {y} = adaptId⤪ (sym (+-assoc w v y))
\end{code}
%</ARL-fin>


%<*intertwine-fin>
\AgdaTarget{intertwine⤪}
\begin{code}
intertwine⤪ : ∀ {a b c d} → ((a + b) + (c + d)) ⤪ ((a + c) + (b + d))
intertwine⤪ {a} {b} {c} {d} =    ALR⤪ {a} {b} {c + d}
                              ⟫⤪ id⤪ {a}  |⤪  ARL⤪ {b}
                              ⟫⤪ id⤪ {a}  |⤪  swap⤪ {b} {c} |⤪ id⤪ {d}
                              ⟫⤪ id⤪ {a}  |⤪  ALR⤪ {c}
                              ⟫⤪ ARL⤪ {a} {c} {b + d}
\end{code}
%</intertwine-fin>


%<*head-fin>
\AgdaTarget{head⤪}
\begin{code}
head⤪ : ∀ {n w} → (suc n * w) ⤪ w
head⤪ {n} {w} = tabulate $ inject+ (n * w)
\end{code}
%</head-fin>


%<*uncons-fin>
\AgdaTarget{uncons⤪}
\begin{code}
uncons⤪ : ∀ {i n} → (suc n * i) ⤪ (i + n * i)
uncons⤪ = id⤪
\end{code}
%</uncons-fin>


%<*cons-fin>
\AgdaTarget{cons⤪}
\begin{code}
cons⤪ : ∀ {i n} → (i + n * i) ⤪ (suc n * i)
cons⤪ = id⤪
\end{code}
%</cons-fin>


%<*singleton-fin>
\AgdaTarget{singleton⤪}
\begin{code}
singleton⤪ : ∀ {w} → w ⤪ (1 * w)
singleton⤪ {w} = adaptId⤪ (sym (+-right-identity w))
\end{code}
%</singleton-fin>


\begin{code}
twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
twiceSuc = solve 2 eq refl where
  eq = λ n w → w :+ (n :+ (con 1 :+ n)) :* w := w :+ n :* w :+ (w :+ n :* w)
\end{code}

%<*vecHalf-fin>
\AgdaTarget{vecHalf⤪}
\begin{code}
vecHalf⤪ : ∀ {n w} → ((2 * suc n) * w) ⤪ (suc n * w + suc n * w)
vecHalf⤪ {n} {w} rewrite +-right-identity n | twiceSuc n w = id⤪
\end{code}
%</vecHalf-fin>


\begin{code}
vecHalfPowEq : ∀ n w → 2 ^ suc n * w  ≡  2 ^ n * w  +  2 ^ n * w
vecHalfPowEq zero w rewrite +-right-identity w = refl
vecHalfPowEq (suc n) w = begin
    2 ^ suc (suc n) * w                 ≡⟨ refl ⟩
    2 * 2 ^ suc n * w                   ≡⟨ *-assoc 2 (2 ^ suc n) w ⟩
    2 * (2 ^ suc n * w)                 ≡⟨ cong (λ x → 2 * x) $ vecHalfPowEq n w ⟩
    2 * (2 ^ n * w  +  2 ^ n * w)       ≡⟨ *-comm 2 (2 ^ n * w + 2 ^ n * w) ⟩
    (2 ^ n * w + 2 ^ n * w) * 2         ≡⟨ distribʳ-*-+ 2 (2 ^ n * w) (2 ^ n * w) ⟩
    2 ^ n * w * 2   +  2 ^ n * w * 2    ≡⟨ (let p = *-comm (2 ^ n * w) 2  in  cong₂ _+_ p p) ⟩
    2 * (2 ^ n * w) +  2 * (2 ^ n * w)  ≡⟨ (let p = sym (*-assoc 2 (2 ^ n) w)  in  cong₂ _+_ p p) ⟩
    2 * 2 ^ n * w   +  2 * 2 ^ n * w    ≡⟨ refl ⟩
    2 ^ suc n * w   +  2 ^ suc n * w
  ∎
\end{code}

%<*vecHalfPow-fin>
\AgdaTarget{vecHalfPow⤪}
\begin{code}
vecHalfPow⤪ : ∀ {n w} → ((2 ^ suc n) * w) ⤪ ((2 ^ n) * w + (2 ^ n) * w)
vecHalfPow⤪ {n} {w} = adaptId⤪ (vecHalfPowEq n w)
\end{code}
%</vecHalfPow-fin>


%<*forkVec-fin>
\AgdaTarget{forkVec⤪}
\begin{code}
forkVec⤪ : ∀ {k n} → n ⤪ (k * n)
forkVec⤪ {k} = concat $ replicate {n = k} (tabulate id)
\end{code}
%</forkVec-fin>


%<*forkProd-fin>
\AgdaTarget{fork×⤪}
\begin{code}
fork×⤪ : ∀ {w} → w ⤪ (w + w)
fork×⤪ = tabulate id ++ tabulate id
\end{code}
%</forkProd-fin>


%<*fst-fin>
\AgdaTarget{fst⤪}
\begin{code}
fst⤪ : ∀ {m n} → (m + n) ⤪ m
fst⤪ {n = n} = tabulate (inject+ n)
\end{code}
%</fst-fin>


%<*snd-fin>
\AgdaTarget{snd⤪}
\begin{code}
snd⤪ : ∀ {m n} → (m + n) ⤪ n
snd⤪ {m} = tabulate (raise m)
\end{code}
%</snd-fin>
