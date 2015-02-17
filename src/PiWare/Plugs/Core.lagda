\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs.Core {At : Atomic} (Gt : Gates At) where

open import Function using (id; _$_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _*_)
open import Data.Nat.DivMod using (_mod_; DivMod; _divMod_)
open import Data.Fin using (Fin; toℕ; inject+; raise)
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (cong; sym; _≡_; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import PiWare.Circuit.Core Gt using (ℂ'X; Plug; _⟫'_; _|'_)

import Algebra as A
import Data.Nat.Properties as N
open import Data.Nat.Properties.Simple using (*-right-zero)
open import Algebra.Operations (A.CommutativeSemiring.semiring N.commutativeSemiring) using (_^_)
open A.CommutativeSemiring N.commutativeSemiring using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)
\end{code}


%<*pSwap-core>
\AgdaTarget{pSwap'}
\begin{code}
pSwap' : ∀ {n m} → ℂ'X (n + m) (m + n)
pSwap' {n} {m} with n + m ≟ 0
pSwap' {n} {m} | yes _ rewrite +-comm n m = Plug id
pSwap' {n} {m} | no ¬z                    = Plug $ finSwap (fromWitnessFalse ¬z)
    where finSwap : False (n + m ≟ 0) → Fin (m + n) → Fin (n + m)
          finSwap ¬z x = _mod_ (toℕ x + m) (n + m) {¬z}
\end{code}
%</pSwap-core>


%<*pid-core>
\AgdaTarget{pid'}
\begin{code}
pid' : ∀ {n} → ℂ'X n n
pid' = Plug id
\end{code}
%</pid-core>


-- associativity plugs
%<*pALR-core>
\AgdaTarget{pALR'}
\begin{code}
pALR' : ∀ {w v y} → ℂ'X ((w + v) + y) (w + (v + y))
pALR' {w} {v} {y} = Plug p
  where p : Fin (w + (v + y)) → Fin ((w + v) + y)
        p x rewrite +-assoc w v y = x
\end{code}
%</pALR-core>

%<*pARL-core>
\AgdaTarget{pARL'}
\begin{code}
pARL' : ∀ {w v y : ℕ} → ℂ'X (w + (v + y)) ((w + v) + y)
pARL' {w} {v} {y} = Plug p
  where p : Fin ((w + v) + y) → Fin (w + (v + y))
        p x rewrite sym (+-assoc w v y) = x
\end{code}
%</pARL-core>

-- TODO: Substitute seq composition by simple Fin → Fin function
%<*pIntertwine-core>
\AgdaTarget{pIntertwine'}
\begin{code}
pIntertwine' : ∀ {a b c d} → ℂ'X ((a + b) + (c + d)) ((a + c) + (b + d))
pIntertwine' {a} {b} {c} {d} = 
       pALR' {a} {b} {c + d}
    ⟫' _|'_ {a} {a} {b + (c + d)} {(b + c) + d}  pid'  (pARL' {b} {c} {d})
    ⟫' _|'_ {a} {a} {(b + c) + d} {(c + b) + d}  pid'  ((pSwap' {b} {c}) |' pid')
    ⟫' _|'_ {a} {a} {(c + b) + d} {c + (b + d)}  pid'  (pALR' {c} {b} {d})
    ⟫'  pARL' {a} {c} {b + d}
\end{code}
%</pIntertwine-core>


%<*pHead-core>
\AgdaTarget{pHead'}
\begin{code}
pHead' : ∀ {n w} → ℂ'X (suc n * w) w
pHead' {n} {w} = Plug (inject+ (n * w))
\end{code}
%</pHead-core>


\begin{code}
open N.SemiringSolver using (solve; _:=_; con; _:+_; _:*_)

twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
twiceSuc = solve 2 eq refl where
  eq = λ n w → w :+ (n :+ (con 1 :+ n)) :* w := w :+ n :* w :+ (w :+ n :* w)
\end{code}

%<*pVecHalf-core>
\AgdaTarget{pVecHalf'}
\begin{code}
pVecHalf' : ∀ {n w} → ℂ'X ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
pVecHalf' {n} {w} rewrite (proj₂ +-identity) n | twiceSuc n w = Plug id
\end{code}
%</pVecHalf-core>


\begin{code}
eqAdd : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
eqAdd a≡c b≡d rewrite a≡c | b≡d = refl

pVecHalfPowEq : ∀ n w → 2 ^ suc n * w  ≡  2 ^ n * w  +  2 ^ n * w
pVecHalfPowEq zero w rewrite (proj₂ +-identity) w = refl
pVecHalfPowEq (suc n) w = begin
    2 ^ suc (suc n) * w                 ≡⟨ refl ⟩
    2 * 2 ^ suc n * w                   ≡⟨ *-assoc 2 (2 ^ suc n) w ⟩
    2 * (2 ^ suc n * w)                 ≡⟨ cong (λ x → 2 * x) $ pVecHalfPowEq n w ⟩
    2 * (2 ^ n * w  +  2 ^ n * w)       ≡⟨ *-comm 2 (2 ^ n * w + 2 ^ n * w) ⟩
    (2 ^ n * w + 2 ^ n * w) * 2         ≡⟨ distribʳ 2 (2 ^ n * w) (2 ^ n * w) ⟩
    2 ^ n * w * 2   +  2 ^ n * w * 2    ≡⟨ (let p = *-comm (2 ^ n * w) 2  in  eqAdd p p) ⟩
    2 * (2 ^ n * w) +  2 * (2 ^ n * w)  ≡⟨ (let p = sym (*-assoc 2 (2 ^ n) w)  in  eqAdd p p) ⟩
    2 * 2 ^ n * w   +  2 * 2 ^ n * w    ≡⟨ refl ⟩
    2 ^ suc n * w   +  2 ^ suc n * w
  ∎
\end{code}

%<*pVecHalfPow-core>
\AgdaTarget{pVecHalfPow'}
\begin{code}
pVecHalfPow' : ∀ {n w} → ℂ'X ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
pVecHalfPow' {n} {w} rewrite pVecHalfPowEq n w = Plug id
\end{code}
%</pVecHalfPow-core>


%<*pFork-core>
\AgdaTarget{pFork'}
\begin{code}
pFork' : ∀ {k n} → ℂ'X n (k * n)
pFork' {k} {zero}  rewrite *-right-zero k = pid'
pFork' {k} {suc m} = Plug (λ x → DivMod.remainder $ (toℕ x) divMod (suc m))
\end{code}
%</pFork-core>


%<*pFst-core>
\AgdaTarget{pFst'}
\begin{code}
pFst' : ∀ {m n} → ℂ'X (m + n) m
pFst' {m} {n} = Plug (inject+ n)
\end{code}
%</pFst-core>


%<*pSnd-core>
\AgdaTarget{pSnd'}
\begin{code}
pSnd' : ∀ {m n} → ℂ'X (m + n) n
pSnd' {m} {n} = Plug (raise m)
\end{code}
%</pSnd-core>
