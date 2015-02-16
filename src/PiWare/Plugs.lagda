\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs {At : Atomic} (Gt : Gates At) where

open import Function using (_$_)
open import Data.Nat using (suc; _+_; _*_)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; proj₂)

open import Algebra as A
open import Data.Nat.Properties as N
open A.CommutativeSemiring N.commutativeSemiring using (+-identity)
open import Algebra.Operations (A.CommutativeSemiring.semiring N.commutativeSemiring) using (_^_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import PiWare.Circuit.Core Gt using (ℂ')
open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-Vec)
open import PiWare.Circuit Gt using (ℂX; Mkℂ; _named_)
open import PiWare.Plugs.Core Gt
  using (pid'; pSwap'; pIntertwine'; pALR'; pARL'; pHead'; pVecHalf'; pVecHalfPow'; pFork'; pFst'; pSnd')
\end{code}


%<*pid>
\AgdaTarget{pid}
\begin{code}
pid : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'
\end{code}
%</pid>


%<*pSwap>
\AgdaTarget{pSwap}
\begin{code}
pSwap : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂX (α × β) (β × α)
pSwap {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sα ⦄ ⦄ (pSwap' {i} {j})
\end{code}
%</pSwap>


%<*pIntertwine>
\AgdaTarget{pIntertwine}
\begin{code}
pIntertwine : ∀ {α i β j γ k δ l} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ ⦃ _ : ⇓W⇑ δ {l} ⦄
              → ℂX ((α × β) × (γ × δ)) ((α × γ) × (β × δ))
pIntertwine {i = i} {j = j} {k = k} {l = l} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        (pIntertwine' {i} {j} {k} {l})
\end{code}
%</pIntertwine>


-- associativity plugs
%<*pALR>
\AgdaTarget{pALR}
\begin{code}
pALR : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ → ℂX ((α × β) × γ) (α × (β × γ))
pALR {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄ (pALR' {i} {j} {k})
\end{code}
%</pALR>


%<*pARL>
\AgdaTarget{pARL}
\begin{code}
pARL : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ → ℂX (α × (β × γ)) ((α × β) × γ)
pARL {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄ (pARL' {i} {j} {k})
\end{code}
%</pARL>
 

-- vector plugs
%<*pHead>
\AgdaTarget{pHead}
\begin{code}
pHead : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (Vec α (suc n)) α
pHead {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ sα ⦄ (pHead' {m} {i})
\end{code}
%</pHead>


%<*pUncons>
\AgdaTarget{pUncons}
\begin{code}
pUncons : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (Vec α (suc n)) (α × Vec α n)
pUncons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ pid'
\end{code}
%</pUncons>


%<*pCons>
\AgdaTarget{pCons}
\begin{code}
pCons : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (α × Vec α n) (Vec α (suc n))
pCons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ pid'
\end{code}
%</pCons>


%<*pSingletonIn>
\AgdaTarget{pSingletonIn}
\begin{code}
pSingletonIn : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX α (Vec α 1)
pSingletonIn {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = 1} ⦃ sα ⦄ ⦄  c'
  where c' : ℂ' i (1 * i)
        c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonIn>


%<*pSingletonOut>
\AgdaTarget{pSingletonOut}
\begin{code}
pSingletonOut : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (Vec α 1) α
pSingletonOut {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ ⇓W⇑-Vec {n = 1} ⦃ sα ⦄ ⦄ ⦃ sα ⦄  c'
  where c' : ℂ' (1 * i) i
        c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonOut>


%<*pVecHalf>
\AgdaTarget{pVecHalt}
\begin{code}
pVecHalf : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
pVecHalf {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓W⇑-Vec {n = 2 * suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦄
        (pVecHalf' {m} {i})
\end{code}
%</pVecHalf>


%<*pVecHalfPow>
\AgdaTarget{pVecHalfPow}
\begin{code}
pVecHalfPow : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
pVecHalfPow {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓W⇑-Vec {n = 2 ^ suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦄ 
        (pVecHalfPow' {m} {i})
\end{code}
%</pVecHalfPow>


%<*pForkVec>
\AgdaTarget{pForkVec}
\begin{code}
pForkVec : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX α (Vec α n)
pForkVec {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ (pFork' {m} {i})
\end{code}
%</pForkVec>


%<*pFork-product>
\AgdaTarget{pFork×}
\begin{code}
pFork× : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → ℂX α (α × α)
pFork× {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sα ⦄ ⦄  c'
  where c' : ℂ' i (i + i)
        c' rewrite sym $ cong (_+_ i) ((proj₂ +-identity) i) = pFork' {2} {i}
\end{code}
%</pFork-product>


-- pairs
%<*pFst>
\AgdaTarget{pFst}
\begin{code}
pFst : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂX (α × β) α
pFst {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sα ⦄ (pFst' {i} {j})
\end{code}
%</pFst>


%<*pSnd>
\AgdaTarget{pSnd}
\begin{code}
pSnd : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → ℂX (α × β) β
pSnd {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sβ ⦄ (pSnd' {i} {j})
\end{code}
%</pSnd>
