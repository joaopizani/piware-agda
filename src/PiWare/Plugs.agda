module PiWare.Plugs (Atom : Set) where

open import Function using (_∘_; _$_; id)
open import Data.Product using (_×_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ; _+_; _*_; suc; zero; _≤?_; _≤_; _≥_; z≤n; s≤s; ≤-pred)
open import Data.Nat.DivMod using (_divMod_; DivMod)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥; raise; inject+)
                     renaming (zero to Fz; suc to Fs)

open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; sym; refl; cong)
open PropEq.≡-Reasoning

open import PiWare.Circuit.Core
open import PiWare.Synthesizable Atom
open import PiWare.Circuit Atom


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

    pSwap' : {α : Set} {n m : ℕ} → Combℂ α (n + m) (m + n)
    pSwap' {_} {n} {m} = Plug (uniteFinSwap ∘ splitFin {m} {n})

    pid' : ∀ {α n} → Combℂ α n n
    pid' = Plug id

    -- associativity plugs
    import Algebra as Alg
    import Data.Nat.Properties as NP
    open import Data.Nat.Properties.Simple using (*-right-zero)
    open import Algebra.Operations (Alg.CommutativeSemiring.semiring NP.commutativeSemiring) using (_^_)
    open module CS = Alg.CommutativeSemiring NP.commutativeSemiring
         using (+-assoc; +-identity; +-comm; *-assoc; *-comm; distribʳ)

    pALR' : {α : Set} {w v y : ℕ} → Combℂ α ((w + v) + y) (w + (v + y))
    pALR' {_} {w} {v} {y} = Plug p
        where p : Fin (w + (v + y)) → Fin ((w + v) + y)
              p x rewrite +-assoc w v y = x

    pARL' : {α : Set} {w v y : ℕ} → Combℂ α (w + (v + y)) ((w + v) + y)
    pARL' {_} {w} {v} {y} = Plug p
        where p : Fin ((w + v) + y) → Fin (w + (v + y))
              p x rewrite sym (+-assoc w v y) = x

    pIntertwine' : {α : Set} {a b c d : ℕ} → Combℂ α ((a + b) + (c + d)) ((a + c) + (b + d))
    pIntertwine' {α} {a} {b} {c} {d} =
            pALR' {α} {a} {b} {c + d}
        >>  _><_ {α} {a} {a} {b + (c + d)} {(b + c) + d}  pid'  (pARL' {α} {b} {c} {d})
        >>  _><_ {α} {a} {a} {(b + c) + d} {(c + b) + d}  pid'  ((pSwap' {α} {b} {c}) >< pid')
        >>  _><_ {α} {a} {a} {(c + b) + d} {c + (b + d)}  pid'  (pALR' {α} {c} {b} {d})
        >>  pARL' {α} {a} {c} {b + d}


    pHead' : {α : Set} {n w : ℕ} → Combℂ α (suc n * w) w
    pHead' {α} {n} {w} = Plug (inject+ (n * w))


    open NP.SemiringSolver using (prove; solve; _:=_; con; var; _:+_; _:*_)

    twiceSuc : ∀ n w → w + (n + suc n) * w ≡ w + n * w + (w + n * w)
    twiceSuc = solve 2 eq refl  -- ring solver creates the equality proof
        where eq = λ n w →  w :+ (n :+ (con 1 :+ n)) :* w  :=  w :+ n :* w :+ (w :+ n :* w)

    pVecHalf' : {α : Set} {n w : ℕ} → Combℂ α ((2 * (suc n)) * w) ((suc n) * w + (suc n) * w)
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
        2 ^ n * w * 2   +  2 ^ n * w * 2   ≡⟨ (let p = *-comm (2 ^ n * w) 2   in  eqAdd p p) ⟩
        2 * (2 ^ n * w) +  2 * (2 ^ n * w) ≡⟨ (let p = sym (*-assoc 2 (2 ^ n) w)  in  eqAdd p p) ⟩
        2 * 2 ^ n * w   +  2 * 2 ^ n * w   ≡⟨ refl ⟩
        2 ^ suc n * w   +  2 ^ suc n * w   ∎

    pVecHalfPow' : {α : Set} {n w : ℕ} → Combℂ α ((2 ^ (suc n)) * w) ((2 ^ n) * w + (2 ^ n) * w)
    pVecHalfPow' {_} {n} {w} rewrite pVecHalfPowEq n w = Plug id


    pFork' : {α : Set} {k n : ℕ} → Combℂ α n (k * n)
    pFork' {_} {k} {zero}  rewrite *-right-zero k = pid'
    pFork' {_} {k} {suc m} = Plug (λ x → DivMod.remainder $ (toℕ x) divMod (suc m))

    pFst' : {α : Set} {m n : ℕ} → Combℂ α (m + n) m
    pFst' {_} {m} {n} = Plug (inject+ n)

    pSnd' : {α : Set} {m n : ℕ} → Combℂ α (m + n) n
    pSnd' {_} {m} {n} = Plug (raise m)



-- identity
pid : {α : Set} {#α : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'


-- rearranging wires
pSwap : {α β : Set} {#α #β : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ → ℂ (α × β) (β × α)
pSwap {#α = #α} {#β = #β} = Mkℂ ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ (pSwap' {Atom} {#α} {#β})


pIntertwine : {α β γ δ : Set} {#α #β #γ #δ : ℕ}
              → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄ ⦃ sδ : ⇓𝕎⇑ δ {#δ} ⦄
              → ℂ  ((α × β) × (γ × δ))  ((α × γ) × (β × δ))
pIntertwine {#α = #α} {#β = #β} {#γ = #γ} {#δ = #δ}  ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄
        (pIntertwine' {Atom} {#α} {#β} {#γ} {#δ})


-- associativity
pALR : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ ((α × β) × γ) (α × (β × γ))
pALR {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄
        (pALR' {Atom} {#α} {#β} {#γ})
        
pARL : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ (α × (β × γ)) ((α × β) × γ)
pARL {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ sγ ⦄ ⦄
        (pARL' {Atom} {#α} {#β} {#γ})
 

-- vector plugs
pHead : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (Vec α (suc n)) α
pHead {_} {#α} {k} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc k} ⦃ sα ⦄ ⦄  ⦃ sα ⦄  (pHead' {Atom} {k} {#α})


pUncons : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (Vec α (suc n)) (α × Vec α n)
pUncons {n = k} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc k} ⦃ sα ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = k} ⦃ sα ⦄ ⦄ ⦄  pid'

⇓𝕎⇑-pUncons-in : {α : Set} {#α : ℕ} {n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (Vec α (suc n))
⇓𝕎⇑-pUncons-in {n = k} ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = suc k}

⇓𝕎⇑-pUncons-out : {α : Set} {#α : ℕ} {n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (α × Vec α n)
⇓𝕎⇑-pUncons-out {n = k} ⦃ sα ⦄ = ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = k} ⦃ sα ⦄ ⦄


pCons : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (α × Vec α n) (Vec α (suc n))
pCons {n = k} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = k} ⦃ sα ⦄ ⦄ ⦄  ⦃ ⇓𝕎⇑-Vec {n = suc k} ⦃ sα ⦄ ⦄  pid'
    

pSingletonIn : {α : Set} {#α : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ α (Vec α 1)
pSingletonIn {_} {#α} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = 1} ⦃ sα ⦄ ⦄  coreC
    where coreC : Combℂ Atom #α (1 * #α)
          coreC rewrite (proj₂ +-identity) #α = pid'

⇓𝕎⇑-pSingletonIn-out : {α : Set} {#α : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ⇓𝕎⇑ (Vec α 1)
⇓𝕎⇑-pSingletonIn-out ⦃ sα ⦄ = ⇓𝕎⇑-Vec {n = 1} ⦃ sα ⦄
          
pSingletonOut : {α : Set} {#α : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (Vec α 1) α
pSingletonOut {_} {#α} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 1} ⦃ sα ⦄ ⦄ ⦃ sα ⦄  coreC
    where coreC : Combℂ Atom (1 * #α) #α
          coreC rewrite (proj₂ +-identity) #α = pid'


pVecHalf : {α : Set} {#α n : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄
           → ℂ (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
pVecHalf {_} {#α} {k} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 * suc k} ⦃ sα ⦄ ⦄
        ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-Vec {n = suc k} ⦃ sα ⦄ ⦄ ⦃ ⇓𝕎⇑-Vec {n = suc k} ⦃ sα ⦄ ⦄ ⦄
        (pVecHalf' {Atom} {k} {#α})


pVecHalfPow : {α : Set} {#α n : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄
              → ℂ (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
pVecHalfPow {_} {#α} {k} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = 2 ^ suc k} ⦃ sα ⦄ ⦄ 
        ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-Vec {n = 2 ^ k} ⦃ sα ⦄ ⦄ ⦃ ⇓𝕎⇑-Vec {n = 2 ^ k} ⦃ sα ⦄ ⦄ ⦄ 
        (pVecHalfPow' {Atom} {k} {#α})


-- forking
pForkVec : {α : Set} {#α k : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ α (Vec α k)
pForkVec {_} {#α} {k} ⦃ sα ⦄ =
    Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = k} ⦃ sα ⦄ ⦄  (pFork' {Atom} {k} {#α})

pFork× : {α : Set} {#α : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ α (α × α)
pFork× {_} {#α} ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ sα ⦄ ⦄  coreC
    where coreC : Combℂ Atom #α (#α + #α)
          coreC rewrite sym $ cong (_+_ #α) ((proj₂ +-identity) #α) = pFork' {Atom} {2} {#α}


-- pairs
pFst : {α β : Set} {#α #β : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ → ℂ (α × β) α
pFst {#α = #α} {#β = #β} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× ⦄ ⦃ sα ⦄ (pFst' {Atom} {#α} {#β})

pSnd : {α β : Set} {#α #β : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ → ℂ (α × β) β
pSnd {#α = #α} {#β = #β} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ ⦃ ⇓𝕎⇑-× ⦄ ⦃ sβ ⦄ (pSnd' {Atom} {#α} {#β})
