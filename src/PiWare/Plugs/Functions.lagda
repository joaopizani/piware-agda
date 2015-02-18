\begin{code}
module PiWare.Plugs.Functions where

open import Function using (id; _∘_; _$_)
open import Data.Nat using (zero; suc; _+_; _*_; _≟_)
open import Data.Fin using (Fin; toℕ; inject+; raise)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product using (proj₂)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (cong; sym; refl; _≡_; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_)

import Algebra as A
import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)
open import Algebra.Operations (A.CommutativeSemiring.semiring N.commutativeSemiring) using (_^_)
open import Data.Nat.Properties.Simple using (*-right-zero)
\end{code}


-- TODO: Fin function "parallel composition"
\begin{code}
postulate _|⤪_ : ∀ {a b c d} → (Fin b → Fin a) → (Fin d → Fin c) → (Fin (b + d) → Fin (a + c))
-- _|⤪_ {a} {b} {c} {d} f g = {!!}

_⟫⤪_ : ∀ {a b c} → (Fin b → Fin a) → (Fin c → Fin b) → (Fin c → Fin a)
f ⟫⤪ g = f ∘ g

infixr 6 _⟫⤪_
infixr 7 _|⤪_
\end{code}



%<*swap-fin>
\begin{code}
swap⤪ : ∀ {n m} → Fin (m + n) → Fin (n + m)
swap⤪ {n} {m} x with n + m ≟ 0
swap⤪ {n} {m} x | yes _ rewrite +-comm n m = x
swap⤪ {n} {m} x | no ¬z = _mod_ (toℕ x + m) (n + m) {fromWitnessFalse ¬z}
\end{code}
%</swap-fin>


%<*ALR-fin>
\begin{code}
ALR⤪ : ∀ {w v y} → Fin (w + (v + y)) → Fin ((w + v) + y)
ALR⤪ {w} {v} {y} rewrite +-assoc w v y = id
\end{code}
%</ALR-fin>


%<*ARL-fin>
\begin{code}
ARL⤪ : ∀ {w v y} → Fin ((w + v) + y) → Fin (w + (v + y))
ARL⤪ {w} {v} {y} rewrite sym (+-assoc w v y) = id
\end{code}
%</ARL-fin>


%<*intertwine-fin>
\begin{code}
intertwine⤪ : ∀ {a b c d} → Fin ((a + c) + (b + d)) → Fin ((a + b) + (c + d))
intertwine⤪ {a} {b} {c} {d} =
       ALR⤪ {a} {b} {c + d}
    ⟫⤪ _|⤪_ {a} {a}  id  (ARL⤪ {b})
    ⟫⤪ _|⤪_ {a} {a}  id  (swap⤪ {b} {c} |⤪ id)
    ⟫⤪ _|⤪_ {a} {a}  id  (ALR⤪ {c})
    ⟫⤪ ARL⤪ {a} {c} {b + d}
\end{code}
%</intertwine-fin>


%<*head-fin>
\begin{code}
head⤪ : ∀ {n w} → Fin w → Fin (suc n * w)
head⤪ {n} {w} = inject+ (n * w)
\end{code}
%</head-fin>


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


%<*fork-fin>
\begin{code}
fork⤪ : ∀ {k n} → Fin (k * n) → Fin n
fork⤪ {k} {zero}  x rewrite *-right-zero k = x
fork⤪ {_} {suc m} x = (toℕ x) mod (suc m)
\end{code}
%</fork-fin>


%<*fst-fin>
\begin{code}
fst⤪ : ∀ {m n} → Fin m → Fin (m + n)
fst⤪ {m} {n} = inject+ n
\end{code}
%</fst-fin>


%<*snd-fin>
\begin{code}
snd⤪ : ∀ {m n} → Fin n → Fin (m + n)
snd⤪ {m} = raise m
\end{code}
%</snd-fin>