\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs.Core {At : Atomic} (Gt : Gates At) where

open import Function using (id; _$_; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _*_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ; inject+; raise)
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (cong; sym; _≡_; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiWare.Circuit.Core Gt using (ℂ'X; Plug; _⟫'_; _|'_)

import Algebra as A
import Data.Nat.Properties as N
open import Data.Nat.Properties.Simple using (*-right-zero)
open import Algebra.Operations (A.CommutativeSemiring.semiring N.commutativeSemiring) using (_^_)
open A.CommutativeSemiring N.commutativeSemiring using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)
\end{code}


%<*id-plug-core>
\AgdaTarget{id⤨'}
\begin{code}
id⤨' : ∀ {n} → ℂ'X n n
id⤨' = Plug id
\end{code}
%</id-plug-core>


%<*swap-fin>
\begin{code}
swap⤪ : ∀ {n m} → ¬ (n + m ≡ 0) → Fin (m + n) → Fin (n + m)
swap⤪ {n} {m} ¬z x = _mod_ (toℕ x + m) (n + m) {fromWitnessFalse ¬z}
\end{code}
%</swap-fin>

%<*swap-plug-core>
\AgdaTarget{swap⤨'}
\begin{code}
swap⤨' : ∀ {n m} → ℂ'X (n + m) (m + n)
swap⤨' {n} {m} with n + m ≟ 0
swap⤨' {n} {m} | yes _ rewrite +-comm n m = id⤨'
swap⤨' {n} {m} | no ¬z                    = Plug (swap⤪ {n} {m} ¬z)
\end{code}
%</swap-plug-core>


-- associativity plugs
%<*ALR-fin>
\begin{code}
ALR⤪ : ∀ {w v y} → Fin (w + (v + y)) → Fin ((w + v) + y)
ALR⤪ {w} {v} {y} rewrite +-assoc w v y = id
\end{code}
%</ALR-fin>

%<*ALR-plug-core>
\AgdaTarget{ALR⤨'}
\begin{code}
ALR⤨' : ∀ {w v y} → ℂ'X ((w + v) + y) (w + (v + y))
ALR⤨' {w} {v} {y} = Plug (ALR⤪ {w} {v} {y})
\end{code}
%</ALR-plug-core>


%<*ARL-fin>
\begin{code}
ARL⤪ : ∀ {w v y} → Fin ((w + v) + y) → Fin (w + (v + y))
ARL⤪ {w} {v} {y} rewrite sym (+-assoc w v y) = id
\end{code}
%</ARL-fin>

%<*ARL-plug-core>
\AgdaTarget{ARL⤨'}
\begin{code}
ARL⤨' : ∀ {w v y : ℕ} → ℂ'X (w + (v + y)) ((w + v) + y)
ARL⤨' {w} {v} {y} = Plug (ARL⤪ {w} {v} {y})
\end{code}
%</ARL-plug-core>


-- TODO: Fin function "parallel composition"
\begin{code}
postulate _|⤪_ : ∀ {a b c d} → (Fin b → Fin a) → (Fin d → Fin c) → (Fin (b + d) → Fin (a + c))
-- _|⤪_ {a} {b} {c} {d} f g = {!!}

_⟫⤪_ : ∀ {a b c} → (Fin b → Fin a) → (Fin c → Fin b) → (Fin c → Fin a)
f ⟫⤪ g = f ∘ g

infixr 6 _⟫⤪_
infixr 7 _|⤪_
\end{code}

%<*intertwine-fin>
\begin{code}
intertwine⤪ : ∀ {a b c d} → Fin ((a + suc c) + (suc b + d)) → Fin ((a + suc b) + (suc c + d))
intertwine⤪ {a} {b} {c} {d} =
       ALR⤪ {a} {suc b} {suc c + d}
    ⟫⤪ _|⤪_ {a} {a}  id  (ARL⤪ {suc b})
    ⟫⤪ _|⤪_ {a} {a}  id  (swap⤪ {suc b} {suc c} (λ ()) |⤪ id)
    ⟫⤪ _|⤪_ {a} {a}  id  (ALR⤪ {suc c})
    ⟫⤪ ARL⤪ {a} {suc c} {suc b + d}
\end{code}
%</intertwine-fin>

%<*intertwine-plug-core>
\AgdaTarget{intertwine⤨'}
\begin{code}
intertwine⤨' : ∀ {a b c d} → ℂ'X ((a + suc b) + (suc c + d)) ((a + suc c) + (suc b + d))
intertwine⤨' {a} {b} {c} {d} = Plug (intertwine⤪ {a} {b} {c} {d})
\end{code}
%</intertwine-plug-core>


%<*head-fin>
\begin{code}
head⤪ : ∀ {n w} → Fin w → Fin (suc n * w)
head⤪ {n} {w} = inject+ (n * w)
\end{code}
%</head-fin>

%<*head-plug-core>
\AgdaTarget{head⤨'}
\begin{code}
head⤨' : ∀ {n w} → ℂ'X (suc n * w) w
head⤨' {n} {w} = Plug (head⤪ {n} {w})
\end{code}
%</head-plug-core>


\begin{code}
open N.SemiringSolver using (solve; _:=_; con; _:+_; _:*_)

twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
twiceSuc = solve 2 eq refl where
  eq = λ n w → w :+ (n :+ (con 1 :+ n)) :* w := w :+ n :* w :+ (w :+ n :* w)
\end{code}

%<*vecHalf-fin>
\begin{code}
vecHalf⤪ : ∀ {n w} → Fin (suc n * w + suc n * w) → Fin ((2 * suc n) * w)
vecHalf⤪ {n} {w} rewrite (proj₂ +-identity) n | twiceSuc n w = id
\end{code}
%</vecHalf-fin>

%<*vecHalf-plug-core>
\AgdaTarget{vecHalf⤨'}
\begin{code}
vecHalf⤨' : ∀ {n w} → ℂ'X ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
vecHalf⤨' {n} {w} = Plug (vecHalf⤪ {n} {w})
\end{code}
%</vecHalf-plug-core>


\begin{code}
eqAdd : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
eqAdd a≡c b≡d rewrite a≡c | b≡d = refl

vecHalfPowEq : ∀ n w → 2 ^ suc n * w  ≡  2 ^ n * w  +  2 ^ n * w
vecHalfPowEq zero w rewrite (proj₂ +-identity) w = refl
vecHalfPowEq (suc n) w = begin
    2 ^ suc (suc n) * w                 ≡⟨ refl ⟩
    2 * 2 ^ suc n * w                   ≡⟨ *-assoc 2 (2 ^ suc n) w ⟩
    2 * (2 ^ suc n * w)                 ≡⟨ cong (λ x → 2 * x) $ vecHalfPowEq n w ⟩
    2 * (2 ^ n * w  +  2 ^ n * w)       ≡⟨ *-comm 2 (2 ^ n * w + 2 ^ n * w) ⟩
    (2 ^ n * w + 2 ^ n * w) * 2         ≡⟨ distribʳ 2 (2 ^ n * w) (2 ^ n * w) ⟩
    2 ^ n * w * 2   +  2 ^ n * w * 2    ≡⟨ (let p = *-comm (2 ^ n * w) 2  in  eqAdd p p) ⟩
    2 * (2 ^ n * w) +  2 * (2 ^ n * w)  ≡⟨ (let p = sym (*-assoc 2 (2 ^ n) w)  in  eqAdd p p) ⟩
    2 * 2 ^ n * w   +  2 * 2 ^ n * w    ≡⟨ refl ⟩
    2 ^ suc n * w   +  2 ^ suc n * w
  ∎
\end{code}

%<*vecHalfPow-fin>
\begin{code}
vecHalfPow⤪ : ∀ {n w} → Fin ((2 ^ n) * w + (2 ^ n) * w) → Fin ((2 ^ suc n) * w)
vecHalfPow⤪ {n} {w} rewrite vecHalfPowEq n w = id
\end{code}
%</vecHalfPow-fin>

%<*vecHalfPow-plug-core>
\AgdaTarget{vecHalfPow⤨'}
\begin{code}
vecHalfPow⤨' : ∀ {n w} → ℂ'X ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
vecHalfPow⤨' {n} {w} = Plug (vecHalfPow⤪ {n} {w})
\end{code}
%</vecHalfPow-plug-core>


%<*fork-fin>
\begin{code}
fork⤪ : ∀ {k n} → Fin (k * (suc n)) → Fin (suc n)
fork⤪ {k} {n} x = (toℕ x) mod (suc n)
\end{code}
%</fork-fin>

%<*fork-plug-core>
\AgdaTarget{fork⤨'}
\begin{code}
fork⤨' : ∀ {k n} → ℂ'X n (k * n)
fork⤨' {k} {zero} rewrite *-right-zero k = id⤨'
fork⤨' {k} {suc m} = Plug (fork⤪ {k} {m})
\end{code}
%</fork-plug-core>


%<*fst-fin>
\begin{code}
fst⤪ : ∀ {m n} → Fin m → Fin (m + n)
fst⤪ {m} {n} = inject+ n
\end{code}
%</fst-fin>

%<*fst-plug-core>
\AgdaTarget{fst⤨'}
\begin{code}
fst⤨' : ∀ {m n} → ℂ'X (m + n) m
fst⤨' {m} {n} = Plug (fst⤪ {m} {n})
\end{code}
%</fst-plug-core>


%<*snd-fin>
\begin{code}
snd⤪ : ∀ {m n} → Fin n → Fin (m + n)
snd⤪ {m} = raise m
\end{code}
%</snd-fin>

%<*snd-plug-core>
\AgdaTarget{snd⤨'}
\begin{code}
snd⤨' : ∀ {m n} → ℂ'X (m + n) n
snd⤨' {m} = Plug (snd⤪ {m})
\end{code}
%</snd-plug-core>
