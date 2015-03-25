\begin{code}
module PiWare.Plugs.Core where

open import Function using (id; _∘′_; _$_)
open import Data.Fin using (Fin; toℕ; inject+; raise; reduce≥; fromℕ≤)
open import Data.Nat.DivMod using (_mod_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (zero; suc; _+_; _*_; _≤?_; _≟_; _≥_; z≤n; s≤s; _≮_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (cong; sym; refl; _≡_; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; _≡⟨_⟩_)

open import Data.Nat.Properties.Simple using (*-right-zero)
open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring; module SemiringSolver to ℕ-SemiringSolver)
open CommutativeSemiring ℕ-commSemiring using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)
open import Algebra.Operations (CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)
open ℕ-SemiringSolver using (solve; _:=_; con; _:+_; _:*_)
open import Data.Product using (proj₂)
+-identityᵣ = proj₂ +-identity

open import PiWare.Interface using (Ix)
\end{code}


\begin{code}
infix 8 _⤪_

_⤪_ : Ix → Ix → Set
i ⤪ o = Fin o → Fin i


≮⇒> : ∀ {n m} → n ≮ m → n ≥ m
≮⇒> {_}     {zero}  _  = z≤n
≮⇒> {zero}  {suc m} ¬p = contradiction (s≤s z≤n) ¬p
≮⇒> {suc n} {suc m} ¬p = s≤s $ ≮⇒> (¬p ∘′ s≤s)

splitFin : ∀ {n m} → Fin (n + m) → Fin n ⊎ Fin m
splitFin {n} x with suc (toℕ x) ≤? n
splitFin     x | yes p  = inj₁ $ fromℕ≤ p
splitFin     x | no  ¬p = inj₂ $ reduce≥ x (≮⇒> ¬p)

_|⤪_ : ∀ {a b c d} → a ⤪ b → c ⤪ d → (a + c) ⤪ (b + d)
_|⤪_ {a} {b} {c} {d} f g = [ (inject+ c) ∘′ f , (raise a) ∘′ g ]′ ∘′ splitFin

_⟫⤪_ : ∀ {a b c} → a ⤪ b → b ⤪ c → a ⤪ c
f ⟫⤪ g = f ∘′ g

infixr 6 _⟫⤪_
infixr 7 _|⤪_
\end{code}



%<*swap-fin>
\AgdaTarget{swap⤪}
\begin{code}
swap⤪ : ∀ {n m} → (n + m) ⤪ (m + n)
swap⤪ {n} {m} x with n + m ≟ 0
swap⤪ {n} {m} x | yes _ rewrite +-comm n m = x
swap⤪ {n} {m} x | no ¬z = _mod_ (toℕ x + m) (n + m) {fromWitnessFalse ¬z}
\end{code}
%</swap-fin>


%<*ALR-fin>
\AgdaTarget{ALR⤪}
\begin{code}
ALR⤪ : ∀ {w v y} → ((w + v) + y) ⤪ (w + (v + y))
ALR⤪ {w} {v} {y} rewrite +-assoc w v y = id
\end{code}
%</ALR-fin>


%<*ARL-fin>
\AgdaTarget{ARL⤪}
\begin{code}
ARL⤪ : ∀ {w v y} → (w + (v + y)) ⤪ ((w + v) + y)
ARL⤪ {w} {v} {y} rewrite sym (+-assoc w v y) = id
\end{code}
%</ARL-fin>


%<*intertwine-fin>
\AgdaTarget{intertwine⤪}
\begin{code}
intertwine⤪ : ∀ {a b c d} → ((a + b) + (c + d)) ⤪ ((a + c) + (b + d))
intertwine⤪ {a} {b} {c} {d} =    ALR⤪ {a} {b} {c + d}
                              ⟫⤪ id {A = Fin a}  |⤪  ARL⤪ {b}
                              ⟫⤪ id {A = Fin a}  |⤪  swap⤪ {b} {c} |⤪ id
                              ⟫⤪ id {A = Fin a}  |⤪  ALR⤪ {c}
                              ⟫⤪ ARL⤪ {a} {c} {b + d}
\end{code}
%</intertwine-fin>


%<*head-fin>
\AgdaTarget{head⤪}
\begin{code}
head⤪ : ∀ {n w} → (suc n * w) ⤪ w
head⤪ {n} {w} = inject+ (n * w)
\end{code}
%</head-fin>


%<*uncons-fin>
\AgdaTarget{uncons⤪}
\begin{code}
uncons⤪ : ∀ {i n} → (suc n * i) ⤪ (i + n * i)
uncons⤪ = id
\end{code}
%</uncons-fin>


%<*cons-fin>
\AgdaTarget{cons⤪}
\begin{code}
cons⤪ : ∀ {i n} → (i + n * i) ⤪ (suc n * i)
cons⤪ = id
\end{code}
%</cons-fin>


%<*singleton-fin>
\AgdaTarget{singleton⤪}
\begin{code}
singleton⤪ : ∀ {w} → w ⤪ (1 * w)
singleton⤪ {w} rewrite +-identityᵣ w = id
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
vecHalf⤪ {n} {w} rewrite +-identityᵣ n | twiceSuc n w = id
\end{code}
%</vecHalf-fin>


\begin{code}
eqAdd : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
eqAdd a≡c b≡d rewrite a≡c | b≡d = refl

vecHalfPowEq : ∀ n w → 2 ^ suc n * w  ≡  2 ^ n * w  +  2 ^ n * w
vecHalfPowEq zero w rewrite +-identityᵣ w = refl
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
\AgdaTarget{vecHalfPow⤪}
\begin{code}
vecHalfPow⤪ : ∀ {n w} → ((2 ^ suc n) * w) ⤪ ((2 ^ n) * w + (2 ^ n) * w)
vecHalfPow⤪ {n} {w} rewrite vecHalfPowEq n w = id
\end{code}
%</vecHalfPow-fin>


%<*forkVec-fin>
\AgdaTarget{forkVec⤪}
\begin{code}
forkVec⤪ : ∀ {k n} → n ⤪ (k * n)
forkVec⤪ {k} {zero}  x rewrite *-right-zero k = x
forkVec⤪ {_} {suc m} x = (toℕ x) mod (suc m)
\end{code}
%</forkVec-fin>


%<*forkProd-fin>
\AgdaTarget{fork×⤪}
\begin{code}
fork×⤪ : ∀ {w} → w ⤪ (w + w)
fork×⤪ {w} rewrite sym $ cong (_+_ w) (+-identityᵣ w) = forkVec⤪ {2} {w}
\end{code}
%</forkProd-fin>


%<*fst-fin>
\AgdaTarget{fst⤪}
\begin{code}
fst⤪ : ∀ {m n} → (m + n) ⤪ m
fst⤪ {m} {n} = inject+ n
\end{code}
%</fst-fin>


%<*snd-fin>
\AgdaTarget{snd⤪}
\begin{code}
snd⤪ : ∀ {m n} → (m + n) ⤪ n
snd⤪ {m} = raise m
\end{code}
%</snd-fin>
