\begin{code}
open import PiWare.Atom

module PiWare.Plugs (At : Atomic) where

open import Data.Vec using (Vec)
open import Function using (_∘_; _$_; id)
open import Data.Product using (_×_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; suc; zero; _≤?_; _≤_; _≥_; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥; raise; inject+) renaming (zero to Fz; suc to Fs)
open import Data.Nat.DivMod using (_divMod_; DivMod)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; sym; refl; cong)
open PropEq.≡-Reasoning

open import PiWare.Utils using (notLEQtoGEQ)
open import PiWare.Synthesizable At
open import PiWare.Circuit.Core
open import PiWare.Circuit At
\end{code}


\begin{code}
private
\end{code}
  %<*splitFin>
  \begin{code}
  splitFin : ∀ {n m} → Fin (n + m) → Fin n ⊎ Fin m
  splitFin {n} {_} x with suc (toℕ x) ≤? n
  splitFin {_} {_} x | yes p  = inj₁ (fromℕ≤ p)
  splitFin {n} {m} x | no  ¬p = inj₂ (reduce≥ {n} {m} x (notLEQtoGEQ ¬p)) 
  \end{code}
  %</splitFin>

  %<*uniteFinSwap>
  \begin{code}
  uniteFinSwap : ∀ {n m} → Fin n ⊎ Fin m → Fin (m + n)
  uniteFinSwap {_} {m} (inj₁ x) = raise   m x
  uniteFinSwap {n} {_} (inj₂ y) = inject+ n y
  \end{code}
  %</uniteFinSwap>

  %<*pSwap'>
  \begin{code}
  pSwap' : ∀ {n m} → ℂ' At (n + m) (m + n)
  pSwap' {n} {m} = Plug (uniteFinSwap ∘ splitFin {m} {n})
  \end{code}
  %</pSwap'>

  %<*pid'>
  \begin{code}
  pid' : ∀ {n} → ℂ' At n n
  pid' = Plug id
  \end{code}
  %</pid'>

  -- associativity plugs
  \begin{code}
  import Algebra as Alg
  import Data.Nat.Properties as NP
  open import Data.Nat.Properties.Simple using (*-right-zero)
  open import Algebra.Operations (Alg.CommutativeSemiring.semiring NP.commutativeSemiring) using (_^_)
  open module CS = Alg.CommutativeSemiring NP.commutativeSemiring
       using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)
  \end{code}

  %<*pALR'>
  \begin{code}
  pALR' : ∀ {w v y} → ℂ' At ((w + v) + y) (w + (v + y))
  pALR' {w} {v} {y} = Plug p  where p : Fin (w + (v + y)) → Fin ((w + v) + y)
                                    p x rewrite +-assoc w v y = x
  \end{code}
  %</pALR'>

  %<*pARL'>
  \begin{code}
  pARL' : ∀ {w v y : ℕ} → ℂ' At (w + (v + y)) ((w + v) + y)
  pARL' {w} {v} {y} = Plug p  where p : Fin ((w + v) + y) → Fin (w + (v + y))
                                    p x rewrite sym (+-assoc w v y) = x
  \end{code}
  %</pARL'>

  -- TODO: Substitute seq composition by simple Fin → Fin function
  %<*pIntertwine'>
  \begin{code}
  pIntertwine' : ∀ {a b c d} → ℂ' At ((a + b) + (c + d)) ((a + c) + (b + d))
  pIntertwine' {a} {b} {c} {d} =
          pALR' {a} {b} {c + d}
      ⟫'  _|'_ {At} {a} {a} {b + (c + d)} {(b + c) + d}  pid'  (pARL' {b} {c} {d})
      ⟫'  _|'_ {At} {a} {a} {(b + c) + d} {(c + b) + d}  pid'  ((pSwap' {b} {c}) |' pid')
      ⟫'  _|'_ {At} {a} {a} {(c + b) + d} {c + (b + d)}  pid'  (pALR' {c} {b} {d})
      ⟫'  pARL' {a} {c} {b + d}
  \end{code}
  %</pIntertwine'>

  %<*pHead'>
  \begin{code}
  pHead' : ∀ {n w} → ℂ' At (suc n * w) w
  pHead' {n} {w} = Plug (inject+ (n * w))
  \end{code}
  %</pHead'>

  \begin{code}
  open NP.SemiringSolver using (solve; _:=_; con; _:+_; _:*_)
  \end{code}

  %<*twiceSuc>
  \begin{code}
  twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
  twiceSuc = solve 2 eq refl  -- ring solver creates the equality proof
      where eq = λ n w →  w :+ (n :+ (con 1 :+ n)) :* w  :=  w :+ n :* w :+ (w :+ n :* w)
  \end{code}
  %</twiceSuc>

  %<*pVecHalf'>
  \begin{code}
  pVecHalf' : ∀ {n w} → ℂ' At ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
  pVecHalf' {n} {w} rewrite (proj₂ +-identity) n | twiceSuc n w = Plug id
  \end{code}
  %</pVecHalf'>

  %<*eqAdd>
  \begin{code}
  eqAdd : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
  eqAdd a≡c b≡d rewrite a≡c | b≡d = refl
  \end{code}
  %</eqAdd>

  %<*pVecHalfPowEq>
  \begin{code}
  pVecHalfPowEq : ∀ n w → 2 ^ suc n * w  ≡  2 ^ n * w  +  2 ^ n * w
  pVecHalfPowEq zero w rewrite (proj₂ +-identity) w = refl
  pVecHalfPowEq (suc n) w = begin
      2 ^ suc (suc n) * w                ≡⟨ refl ⟩
      2 * 2 ^ suc n * w                  ≡⟨ *-assoc 2 (2 ^ suc n) w ⟩
      2 * (2 ^ suc n * w)                ≡⟨ cong (λ x → 2 * x) $ pVecHalfPowEq n w ⟩
      2 * (2 ^ n * w  +  2 ^ n * w)      ≡⟨ *-comm 2 (2 ^ n * w + 2 ^ n * w) ⟩
      (2 ^ n * w + 2 ^ n * w) * 2        ≡⟨ distribʳ 2 (2 ^ n * w) (2 ^ n * w) ⟩
      2 ^ n * w * 2   +  2 ^ n * w * 2   ≡⟨ (let p = *-comm (2 ^ n * w) 2       in  eqAdd p p) ⟩
      2 * (2 ^ n * w) +  2 * (2 ^ n * w) ≡⟨ (let p = sym (*-assoc 2 (2 ^ n) w)  in  eqAdd p p) ⟩
      2 * 2 ^ n * w   +  2 * 2 ^ n * w   ≡⟨ refl ⟩
      2 ^ suc n * w   +  2 ^ suc n * w   ∎
  \end{code}
  %</pVecHalfPowEq>

  %<*pVecHalfPow'>
  \begin{code}
  pVecHalfPow' : ∀ {n w} → ℂ' At ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
  pVecHalfPow' {n} {w} rewrite pVecHalfPowEq n w = Plug id
  \end{code}
  %</pVecHalfPow'>

  %<*pFork'>
  \begin{code}
  pFork' : ∀ {k n} → ℂ' At n (k * n)
  pFork' {k} {zero}  rewrite *-right-zero k = pid'
  pFork' {k} {suc m} = Plug (λ x → DivMod.remainder $ (toℕ x) divMod (suc m))
  \end{code}
  %</pFork'>

  %<*pFst'>
  \begin{code}
  pFst' : ∀ {m n} → ℂ' At (m + n) m
  pFst' {m} {n} = Plug (inject+ n)
  \end{code}
  %</pFst'>

  %<*pSnd'>
  \begin{code}
  pSnd' : ∀ {m n} → ℂ' At (m + n) n
  pSnd' {m} {n} = Plug (raise m)
  \end{code}
  %</pSnd'>


-- identity
%<*pid>
\begin{code}
pid : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'
\end{code}
%</pid>

-- rearranging wires
%<*pSwap>
\begin{code}
pSwap : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) (β × α)
pSwap {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ ⇓𝕎⇑-× sβ sα ⦄ (pSwap' {i} {j})
\end{code}
%</pSwap>


%<*pIntertwine>
\begin{code}
pIntertwine : ∀ {α i β j γ k δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
              → ℂ  ((α × β) × (γ × δ))  ((α × γ) × (β × δ))
pIntertwine {i = i} {j = j} {k = k} {l = l}  ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) (⇓𝕎⇑-× sγ sδ) ⦄  ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sγ) (⇓𝕎⇑-× sβ sδ) ⦄
        (pIntertwine' {i} {j} {k} {l})
\end{code}
%</pIntertwine>


-- associativity
%<*pALR>
\begin{code}
pALR : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ ((α × β) × γ) (α × (β × γ))
pALR {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ ⦄ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-× sβ sγ) ⦄ (pALR' {i} {j} {k})
\end{code}
%</pALR>

%<*pARL>
\begin{code}
pARL : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ (α × (β × γ)) ((α × β) × γ)
pARL {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-× sβ sγ) ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ ⦄ (pARL' {i} {j} {k})
\end{code}
%</pARL>
 

-- vector plugs
%<*pHead>
\begin{code}
pHead : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (suc n)) α
pHead {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ ⦃ sα ⦄ (pHead' {m} {i})
\end{code}
%</pHead>


%<*pUncons>
\begin{code}
pUncons : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (suc n)) (α × Vec α n)
pUncons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα) ⦄ pid'
\end{code}
%</pUncons>

%<*Synth-pUncons-in>
\begin{code}
⇓𝕎⇑-pUncons-in : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (Vec α (suc n))
⇓𝕎⇑-pUncons-in {n = m} ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = suc m} sα
\end{code}
%</Synth-pUncons-in>

%<*Synth-pUncons-out>
\begin{code}
⇓𝕎⇑-pUncons-out : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (α × Vec α n)
⇓𝕎⇑-pUncons-out {n = m} ⦃ sα ⦄ = ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα)
\end{code}
%</Synth-pUncons-out>


%<*pCons>
\begin{code}
pCons : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (α × Vec α n) (Vec α (suc n))
pCons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα) ⦄ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ pid'
\end{code}
%</pCons>


%<*pSingletonIn>
\begin{code}
pSingletonIn : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (Vec α 1)
pSingletonIn {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = 1} sα ⦄  c'
    where c' : ℂ' At i (1 * i)
          c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonIn>

%<*Synth-pSingletonIn-out>
\begin{code}
⇓𝕎⇑-pSingletonIn-out : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (Vec α 1)
⇓𝕎⇑-pSingletonIn-out ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = 1} sα
\end{code}
%</Synth-pSingletonIn-out>

%<*pSingletonOut>
\begin{code}
pSingletonOut : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α 1) α
pSingletonOut {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 1} sα ⦄ ⦃ sα ⦄  c'
    where c' : ℂ' At (1 * i) i
          c' rewrite (proj₂ +-identity) i = pid'
\end{code}
%</pSingletonOut>


%<*pVecHalf>
\begin{code}
pVecHalf : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
pVecHalf {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 * suc m} sα ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-Vec {n = suc m} sα) (⇓𝕎⇑-Vec {n = suc m} sα) ⦄
        (pVecHalf' {m} {i})
\end{code}
%</pVecHalf>


%<*pVecHalfPow>
\begin{code}
pVecHalfPow : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
pVecHalfPow {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 ^ suc m} sα ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-Vec {n = 2 ^ m} sα) (⇓𝕎⇑-Vec {n = 2 ^ m} sα) ⦄ 
        (pVecHalfPow' {m} {i})
\end{code}
%</pVecHalfPow>


%<*pForkVec>
\begin{code}
pForkVec : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (Vec α n)
pForkVec {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = m} sα ⦄ (pFork' {m} {i})
\end{code}
%</pForkVec>

%<*pFork-product>
\begin{code}
pFork× : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (α × α)
pFork× {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× sα sα ⦄  c'
    where c' : ℂ' At i (i + i)
          c' rewrite sym $ cong (_+_ i) ((proj₂ +-identity) i) = pFork' {2} {i}
\end{code}
%</pFork-product>


-- pairs
%<*pFst>
\begin{code}
pFst : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) α
pFst {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ sα ⦄ (pFst' {i} {j})
\end{code}
%</pFst>

%<*pSnd>
\begin{code}
pSnd : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) β
pSnd {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ sβ ⦄ (pSnd' {i} {j})
\end{code}
%</pSnd>
