\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs {At : Atomic} (Gt : Gates At) where

open import Function using (_$_)
open import Data.Nat using (suc; _+_; _*_)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; proj₂)

open import Algebra as A
open import Data.Nat.Properties as NP
open module CS = A.CommutativeSemiring NP.commutativeSemiring using (+-identity)
open import Algebra.Operations (A.CommutativeSemiring.semiring NP.commutativeSemiring) using (_^_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import PiWare.Circuit.Core Gt using (ℂ')
open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-Vec)
open import PiWare.Circuit Gt using (ℂ; Mkℂ; _named_)
open import PiWare.Plugs.Core Gt
    using (pid'; pSwap'; pIntertwine'; pALR'; pARL'; pHead'; pVecHalf'; pVecHalfPow'; pFork'; pFst'; pSnd')
\end{code}


-- identity
%<*pid>
\begin{code}
pid pid^ : ∀ {α i} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ α α
pid^ {i = i} = pid {i = i} named "pid"
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'
\end{code}
%</pid>

-- rearranging wires
%<*pSwap>
\begin{code}
pSwap pSwap^ : ∀ {α i β j} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ (α × β) (β × α)
pSwap^ {i = i} {j = j} = pSwap {i = i} {j = j} named "pSwap"
pSwap {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sα ⦄ ⦄ (pSwap' {i} {j})
\end{code}
%</pSwap>


%<*pIntertwine>
\begin{code}
pIntertwine pIntertwine^ : ∀ {α i β j γ k δ l}
    → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ ⦃ sδ : ⇓W⇑ δ {l} ⦄
    → ℂ  ((α × β) × (γ × δ))  ((α × γ) × (β × δ))
pIntertwine^ {i = i} {j = j} {k = k} {l = l} = pIntertwine {i = i} {j = j} {k = k} {l = l} named "pIntertwine"
pIntertwine {i = i} {j = j} {k = k} {l = l}  ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        (pIntertwine' {i} {j} {k} {l})
\end{code}
%</pIntertwine>


-- associativity
%<*pALR>
\begin{code}
pALR pALR^ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
    → ℂ ((α × β) × γ) (α × (β × γ))
pALR^ {i = i} {j = j} {k = k} = pALR {i = i} {j = j} {k = k} named "pALR"
pALR {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄
        (pALR' {i} {j} {k})
\end{code}
%</pALR>

%<*pARL>
\begin{code}
pARL pARL^ : ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄
    → ℂ (α × (β × γ)) ((α × β) × γ)
pARL^ {i = i} {j = j} {k = k} = pARL {i = i} {j = j} {k = k} named "pARL"
pARL {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄
        (pARL' {i} {j} {k})
\end{code}
%</pARL>
 

-- vector plugs
%<*pHead>
\begin{code}
pHead pHead^ : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (Vec α (suc n)) α
pHead^ {i = i} = pHead {i = i} named "pHead"
pHead {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ sα ⦄ (pHead' {m} {i})
\end{code}
%</pHead>

%<*pUncons>
\begin{code}
pUncons pUncons^ : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (Vec α (suc n)) (α × Vec α n)
pUncons^ {i = i} = pUncons {i = i} named "pUncons"
pUncons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ pid'
\end{code}
%</pUncons>

%<*pCons>
\begin{code}
pCons pCons^ : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (α × Vec α n) (Vec α (suc n))
pCons^ {i = i} = pCons {i = i} named "pCons"
pCons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ pid'
\end{code}
%</pCons>

%<*pSingletonIn>
\begin{code}
pSingletonIn pSingletonIn^ : ∀ {α i} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ α (Vec α 1)
pSingletonIn^ {i = i} = pSingletonIn {i = i} named "pSingleton"
pSingletonIn {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = 1} ⦃ sα ⦄ ⦄  c'
    where c' : ℂ' i (1 * i)
          c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonIn>

%<*pSingletonOut>
\begin{code}
pSingletonOut pSingletonOut^ : ∀ {α i} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (Vec α 1) α
pSingletonOut^ {i = i} = pSingletonOut {i = i} named "pSingletonOut"
pSingletonOut {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = 1} ⦃ sα ⦄ ⦄ ⦃ sα ⦄  c'
    where c' : ℂ' (1 * i) i
          c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonOut>


%<*pVecHalf>
\begin{code}
pVecHalf pVecHalf^ : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
pVecHalf^ {i = i} = pVecHalf {i = i} named "pVecHalf"
pVecHalf {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓W⇑-Vec {n = 2 * suc m} ⦃ sα ⦄ ⦄
        ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦄
        (pVecHalf' {m} {i})
\end{code}
%</pVecHalf>

%<*pVecHalfPow>
\begin{code}
pVecHalfPow pVecHalfPow^ :
    ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
pVecHalfPow^ {α} {i} {m} ⦃ sα ⦄ = pVecHalfPow {α} {i} {m} ⦃ sα ⦄ named "pVecHalfPow"
pVecHalfPow {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓W⇑-Vec {n = 2 ^ suc m} ⦃ sα ⦄ ⦄
        ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦄ 
        (pVecHalfPow' {m} {i})
\end{code}
%</pVecHalfPow>


%<*pForkVec>
\begin{code}
pForkVec pForkVec^ : ∀ {α i n} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ α (Vec α n)
pForkVec^ {i = i} = pForkVec {i = i} named "pForkVec"
pForkVec {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ (pFork' {m} {i})
\end{code}
%</pForkVec>

%<*pFork-product>
\begin{code}
pFork× pFork×^ : ∀ {α i} → ⦃ sα : ⇓W⇑ α {i} ⦄ → ℂ α (α × α)
pFork×^ {i = i} = pFork× {i = i} named "pFork×"
pFork× {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sα ⦄ ⦄  c'
    where c' : ℂ' i (i + i)
          c' rewrite sym $ cong (_+_ i) ((proj₂ +-identity) i) = pFork' {2} {i}
\end{code}
%</pFork-product>


-- pairs
%<*pFst>
\begin{code}
pFst pFst^ : ∀ {α i β j} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ (α × β) α
pFst^ {i = i} {j = j} = pFst {i = i} {j = j} named "pFst"
pFst {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sα ⦄ (pFst' {i} {j})
\end{code}
%</pFst>

%<*pSnd>
\begin{code}
pSnd pSnd^ : ∀ {α i β j} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ → ℂ (α × β) β
pSnd^ {i = i} {j = j} = pSnd {i = i} {j = j} named "pSnd"
pSnd {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sβ ⦄ (pSnd' {i} {j})
\end{code}
%</pSnd>
