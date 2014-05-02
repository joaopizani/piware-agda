module PiWare.Plugs where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _+_; _*_; suc; _≤?_; _≤_; _≥_)
open import Data.Nat.DivMod using (_divMod_; DivMod)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥; raise; inject+)
                     renaming (zero to Fz; suc to Fs)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Data.Vec using (Vec)
open import Function using (_∘_; id)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬¬_)
open import Relation.Binary.PropositionalEquality using (sym)

open import PiWare.Circuit 




-- Plugs
private
    postulate massageInequality : {n m : ℕ} → ¬¬ (suc n ≤ m) → (n ≥ m)

    splitFin : ∀ {n m} → Fin (n + m) → Fin n ⊎ Fin m
    splitFin {n} {_} x with suc (toℕ x) ≤? n
    splitFin {_} {_} x | yes proof = inj₁ (fromℕ≤ proof)
    splitFin {n} {m} x | no  proof = inj₂ (reduce≥ {n} {m} x (massageInequality proof)) 

    uniteFinSwap : ∀ {n m} → Fin n ⊎ Fin m → Fin (m + n)
    uniteFinSwap {_} {m} (inj₁ x) = raise   m x
    uniteFinSwap {n} {_} (inj₂ y) = inject+ n y

    pSwap' : {α : Set} {n m : ℕ} → Coreℂ α (n + m) (m + n)
    pSwap' {_} {n} {m} = Plug p
        where p : Fin (m + n) → Fin (n + m)
              p = uniteFinSwap ∘ splitFin {m} {n}

    pid' : ∀ {α n} → Coreℂ α n n
    pid' = Plug id

    import Algebra as Alg
    import Data.Nat.Properties as NP
    open module CS = Alg.CommutativeSemiring NP.commutativeSemiring using (+-assoc)

    pALR' : {α : Set} {w v y : ℕ} → Coreℂ α ((w + v) + y) (w + (v + y))
    pALR' {_} {w} {v} {y} = Plug p
        where p : Fin (w + (v + y)) → Fin ((w + v) + y)
              p x rewrite +-assoc w v y = x
              
    pARL' : {α : Set} {w v y : ℕ} → Coreℂ α (w + (v + y)) ((w + v) + y)
    pARL' {_} {w} {v} {y} = Plug p
        where p : Fin ((w + v) + y) → Fin (w + (v + y))
              p x rewrite sym (+-assoc w v y) = x

    pIntertwine' : {α : Set} {a b c d : ℕ} → Coreℂ α ((a + b) + (c + d)) ((a + c) + (b + d))
    pIntertwine' {α} {a} {b} {c} {d} =
            pALR' {α} {a} {b} {c + d}
        >>  _><_ {α} {a} {a} {b + (c + d)} {(b + c) + d}  pid'  (pARL' {α} {b} {c} {d})
        >>  _><_ {α} {a} {a} {(b + c) + d} {(c + b) + d}  pid'  ((pSwap' {α} {b} {c}) >< pid')
        >>  _><_ {α} {a} {a} {(c + b) + d} {c + (b + d)}  pid'  (pALR' {α} {c} {b} {d})
        >>  pARL' {α} {a} {c} {b + d}

    pHead' : {α : Set} {n w : ℕ} → Coreℂ α (suc n * w) w
    pHead' {α} {n} {w} = Plug p
        where p : Fin w → Fin (suc n * w)
              p x = inject+ (n * w) x

    pFork' : {α : Set} {n k : ℕ} → Coreℂ α (suc n) (k * suc n)
    pFork' {α} {n} {k} = Plug p
        where p : Fin (k * suc n) → Fin (suc n)
              p x = DivMod.remainder ((toℕ x) divMod (suc n))


pSwap : {α β : Set} {#α #β : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ → ℂ (α × β) (β × α)
pSwap {#α = #α} {#β = #β} = Mkℂ ⦃ ⇓𝕎⇑-× ⦄ ⦃ ⇓𝕎⇑-× ⦄ (pSwap' {𝔹} {#α} {#β})


pid : {α : Set} {#α : ℕ} ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'


pALR : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ ((α × β) × γ) (α × (β × γ))
pALR {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄
        (pALR' {𝔹} {#α} {#β} {#γ})
        

pARL : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ ⦃ sβ : ⇓𝕎⇑ β {#β} ⦄ ⦃ sγ : ⇓𝕎⇑ γ {#γ} ⦄
       → ℂ (α × (β × γ)) ((α × β) × γ)
pARL {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-× ⦄ ⦄ ⦃ ⇓𝕎⇑-× ⦃ ⇓𝕎⇑-× ⦄ ⦃ sγ ⦄ ⦄
        (pARL' {𝔹} {#α} {#β} {#γ})
        

pHead : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (Vec α (suc n)) α
pHead {_} {#α} {n} ⦃ sα ⦄ = Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc n} ⦃ sα ⦄ ⦄  ⦃ sα ⦄  (pHead' {𝔹} {n} {#α})


pUncons : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (Vec α (suc n)) (α × Vec α n)
pUncons {n = n} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-Vec {n = suc n} ⦃ sα ⦄ ⦄  ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = n} ⦃ sα ⦄ ⦄ ⦄  pid'


pCons : {α : Set} {#α n : ℕ} → ⦃ sα : ⇓𝕎⇑ α {#α} ⦄ → ℂ (α × Vec α n) (Vec α (suc n))
pCons {n = n} ⦃ sα ⦄ =
    Mkℂ ⦃ ⇓𝕎⇑-× ⦃ sα ⦄ ⦃ ⇓𝕎⇑-Vec {n = n} ⦃ sα ⦄ ⦄ ⦄  ⦃ ⇓𝕎⇑-Vec {n = suc n} ⦃ sα ⦄ ⦄  pid'
