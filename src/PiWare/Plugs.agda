open import PiWare.Atom

module PiWare.Plugs (AI : AtomInfo) where

open module AI' = AtomInfo AI

open import Data.Vec using (Vec)
open import Function using (_∘_; _$_; id)
open import Data.Product using (_×_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; suc; zero; _≤?_; _≤_; _≥_; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥; raise; inject+) renaming (zero to Fz; suc to Fs)
open import Data.Nat.DivMod using (_divMod_; DivMod)

open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; sym; refl; cong)
open PropEq.≡-Reasoning

open import PiWare.Circuit.Core
open import PiWare.Synthesizable AI
open import PiWare.Circuit AI


private
    notLEQtoGEQ : {n m : ℕ} → ¬ (suc n ≤ m) → (n ≥ m)
    notLEQtoGEQ {_}     {zero}  _  = z≤n
    notLEQtoGEQ {zero}  {suc m} ¬p = contradiction (s≤s z≤n) ¬p
    notLEQtoGEQ {suc n} {suc m} ¬p = s≤s $ notLEQtoGEQ (¬p ∘ s≤s)

    splitFin : ∀ {n m} → Fin (n + m) → Fin n ⊎ Fin m
    splitFin {n} {_} x with suc (toℕ x) ≤? n
    splitFin {_} {_} x | yes p  = inj₁ (fromℕ≤ p)
    splitFin {n} {m} x | no  ¬p = inj₂ (reduce≥ {n} {m} x (notLEQtoGEQ ¬p)) 

    uniteFinSwap : ∀ {n m} → Fin n ⊎ Fin m → Fin (m + n)
    uniteFinSwap {_} {m} (inj₁ x) = raise   m x
    uniteFinSwap {n} {_} (inj₂ y) = inject+ n y

    pSwap' : {α : Set} {n m : ℕ} → ℂ' α (n + m) (m + n)
    pSwap' {_} {n} {m} = Plug (uniteFinSwap ∘ splitFin {m} {n})

    pid' : ∀ {α n} → ℂ' α n n
    pid' = Plug id

    -- associativity plugs
    import Algebra as Alg
    import Data.Nat.Properties as NP
    open import Data.Nat.Properties.Simple using (*-right-zero)
    open import Algebra.Operations (Alg.CommutativeSemiring.semiring NP.commutativeSemiring) using (_^_)
    open module CS = Alg.CommutativeSemiring NP.commutativeSemiring
         using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)

    pALR' : {α : Set} {w v y : ℕ} → ℂ' α ((w + v) + y) (w + (v + y))
    pALR' {_} {w} {v} {y} = Plug p
        where p : Fin (w + (v + y)) → Fin ((w + v) + y)
              p x rewrite +-assoc w v y = x

    pARL' : {α : Set} {w v y : ℕ} → ℂ' α (w + (v + y)) ((w + v) + y)
    pARL' {_} {w} {v} {y} = Plug p
        where p : Fin ((w + v) + y) → Fin (w + (v + y))
              p x rewrite sym (+-assoc w v y) = x

    pIntertwine' : {α : Set} {a b c d : ℕ} → ℂ' α ((a + b) + (c + d)) ((a + c) + (b + d))
    pIntertwine' {α} {a} {b} {c} {d} =
            pALR' {α} {a} {b} {c + d}
        ⟫'  _|'_ {α} {a} {a} {b + (c + d)} {(b + c) + d}  pid'  (pARL' {α} {b} {c} {d})
        ⟫'  _|'_ {α} {a} {a} {(b + c) + d} {(c + b) + d}  pid'  ((pSwap' {α} {b} {c}) |' pid')
        ⟫'  _|'_ {α} {a} {a} {(c + b) + d} {c + (b + d)}  pid'  (pALR' {α} {c} {b} {d})
        ⟫'  pARL' {α} {a} {c} {b + d}


    pHead' : {α : Set} {n w : ℕ} → ℂ' α (suc n * w) w
    pHead' {α} {n} {w} = Plug (inject+ (n * w))


    open NP.SemiringSolver using (prove; solve; _:=_; con; var; _:+_; _:*_)

    twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
    twiceSuc = solve 2 eq refl  -- ring solver creates the equality proof
        where eq = λ n w →  w :+ (n :+ (con 1 :+ n)) :* w  :=  w :+ n :* w :+ (w :+ n :* w)

    pVecHalf' : {α : Set} {n w : ℕ} → ℂ' α ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
    pVecHalf' {_} {n} {w} rewrite (proj₂ +-identity) n | twiceSuc n w = Plug id


    eqAdd : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
    eqAdd a≡c b≡d rewrite a≡c | b≡d = refl

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

    pVecHalfPow' : {α : Set} {n w : ℕ} → ℂ' α ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
    pVecHalfPow' {_} {n} {w} rewrite pVecHalfPowEq n w = Plug id


    pFork' : {α : Set} {k n : ℕ} → ℂ' α n (k * n)
    pFork' {_} {k} {zero}  rewrite *-right-zero k = pid'
    pFork' {_} {k} {suc m} = Plug (λ x → DivMod.remainder $ (toℕ x) divMod (suc m))

    pFst' : {α : Set} {m n : ℕ} → ℂ' α (m + n) m
    pFst' {_} {m} {n} = Plug (inject+ n)

    pSnd' : {α : Set} {m n : ℕ} → ℂ' α (m + n) n
    pSnd' {_} {m} {n} = Plug (raise m)



-- identity
pid : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'


-- rearranging wires
pSwap : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) (β × α)
pSwap {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ ⇓𝕎⇑-× sβ sα ⦄ (pSwap' {Atom} {i} {j})


pIntertwine : ∀ {α i β j γ k δ l} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {l} ⦄
              → ℂ  ((α × β) × (γ × δ))  ((α × γ) × (β × δ))
pIntertwine {i = i} {j = j} {k = k} {l = l}  ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) (⇓𝕎⇑-× sγ sδ) ⦄  ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sγ) (⇓𝕎⇑-× sβ sδ) ⦄
        (pIntertwine' {Atom} {i} {j} {k} {l})


-- associativity
pALR : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ ((α × β) × γ) (α × (β × γ))
pALR {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ ⦄ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-× sβ sγ) ⦄ (pALR' {Atom} {i} {j} {k})
        
pARL : ∀ {α i β j γ k} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {k} ⦄
       → ℂ (α × (β × γ)) ((α × β) × γ)
pARL {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-× sβ sγ) ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ ⦄ (pARL' {Atom} {i} {j} {k})
 

-- vector plugs
pHead : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (suc n)) α
pHead {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ ⦃ sα ⦄ (pHead' {Atom} {m} {i})


pUncons : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (suc n)) (α × Vec α n)
pUncons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα) ⦄ pid'

⇓𝕎⇑-pUncons-in : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (Vec α (suc n))
⇓𝕎⇑-pUncons-in {n = m} ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = suc m} sα

⇓𝕎⇑-pUncons-out : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (α × Vec α n)
⇓𝕎⇑-pUncons-out {n = m} ⦃ sα ⦄ = ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα)


pCons : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (α × Vec α n) (Vec α (suc n))
pCons {n = m} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα (⇓𝕎⇑-Vec {n = m} sα) ⦄ ⦃ ⇓𝕎⇑-Vec {n = suc m} sα ⦄ pid'
    

pSingletonIn : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (Vec α 1)
pSingletonIn {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = 1} sα ⦄  c'
    where c' : ℂ' Atom i (1 * i)
          c' rewrite (proj₂ +-identity) i = pid'

⇓𝕎⇑-pSingletonIn-out : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ⇓𝕎⇑ (Vec α 1)
⇓𝕎⇑-pSingletonIn-out ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = 1} sα
          
pSingletonOut : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α 1) α
pSingletonOut {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 1} sα ⦄ ⦃ sα ⦄  c'
    where c' : ℂ' Atom (1 * i) i
          c' rewrite (proj₂ +-identity) i = pid'


pVecHalf : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
pVecHalf {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 * suc m} sα ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-Vec {n = suc m} sα) (⇓𝕎⇑-Vec {n = suc m} sα) ⦄
        (pVecHalf' {Atom} {m} {i})


pVecHalfPow : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
pVecHalfPow {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 ^ suc m} sα ⦄ ⦃ ⇓𝕎⇑-× (⇓𝕎⇑-Vec {n = 2 ^ m} sα) (⇓𝕎⇑-Vec {n = 2 ^ m} sα) ⦄ 
        (pVecHalfPow' {Atom} {m} {i})


-- forking (TODO: non-empty vectors)
pForkVec : ∀ {α i n} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (Vec α n)
pForkVec {_} {i} {m} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = m} sα ⦄ (pFork' {Atom} {m} {i})

pFork× : ∀ {α i} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ → ℂ α (α × α)
pFork× {_} {i} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× sα sα ⦄  c'
    where c' : ℂ' Atom i (i + i)
          c' rewrite sym $ cong (_+_ i) ((proj₂ +-identity) i) = pFork' {Atom} {2} {i}


-- pairs
pFst : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) α
pFst {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ sα ⦄ (pFst' {Atom} {i} {j})

pSnd : ∀ {α i β j} → ⦃ sα : ⇓𝕎⇑ α {i} ⦄ ⦃ sβ : ⇓𝕎⇑ β {j} ⦄ → ℂ (α × β) β
pSnd {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× sα sβ ⦄ ⦃ sβ ⦄ (pSnd' {Atom} {i} {j})
