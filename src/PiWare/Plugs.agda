module PiWare.Plugs where

open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _+_; suc; _≤?_; _≤_; _≥_)
open import Data.Fin using (Fin; toℕ; fromℕ≤; reduce≥; raise; inject+)
                     renaming (zero to Fz; suc to Fs)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Function using (_∘_; id)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬¬_)
open import Relation.Binary.PropositionalEquality using (sym)

open import PiWare.Circuit 




-- Plugs
private
    splitFin : ∀ {n m} → Fin (n + m) → Fin n ⊎ Fin m
    splitFin {n} {_} x with suc (toℕ x) ≤? n
    splitFin {_} {_} x | yes proof = inj₁ (fromℕ≤ proof)
    splitFin {n} {m} x | no  proof = inj₂ (reduce≥ {n} {m} x (massageInequality proof)) 
        where massageInequality : {n m : ℕ} → ¬¬ (suc n ≤ m) → (n ≥ m)
              massageInequality {n} {m} ineq = {!!}

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

    
pSwap : {α β : Set} {#α #β : ℕ} ⦃ sα : Synth α {#α} ⦄ ⦃ sβ : Synth β {#β} ⦄ → ℂ (α × β) (β × α)
pSwap {#α = #α} {#β = #β} = Mkℂ ⦃ synthPair ⦄ ⦃ synthPair ⦄ (pSwap' {𝔹} {#α} {#β})


pid : {α : Set} {#α : ℕ} ⦃ sα : Synth α {#α} ⦄ → ℂ α α
pid ⦃ sα ⦄ = Mkℂ ⦃ sα ⦄ ⦃ sα ⦄ pid'


pALR : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : Synth α {#α} ⦄ ⦃ sβ : Synth β {#β} ⦄ ⦃ sγ : Synth γ {#γ} ⦄
       → ℂ ((α × β) × γ) (α × (β × γ))
pALR {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ synthPair ⦃ synthPair ⦄ ⦃ sγ ⦄ ⦄ ⦃ synthPair ⦃ sα ⦄ ⦃ synthPair ⦄ ⦄
        (pALR' {𝔹} {#α} {#β} {#γ})
        

pARL : {α β γ : Set} {#α #β #γ : ℕ}
       → ⦃ sα : Synth α {#α} ⦄ ⦃ sβ : Synth β {#β} ⦄ ⦃ sγ : Synth γ {#γ} ⦄
       → ℂ (α × (β × γ)) ((α × β) × γ)
pARL {#α = #α} {#β = #β} {#γ = #γ} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ ⦃ synthPair ⦃ sα ⦄ ⦃ synthPair ⦄ ⦄ ⦃ synthPair ⦃ synthPair ⦄ ⦃ sγ ⦄ ⦄
        (pARL' {𝔹} {#α} {#β} {#γ})


-- pComm : {α : Set} {w v : ℕ} → ℂ α (w + v) (v + w)
-- pComm {_} {w} {v} = Plug pComm'
--     where pComm' : Fin (v + w) → Fin (w + v)
--           pComm' x rewrite CS.+-comm w v = x

-- -- Is not actually intertwining. Size-only indices don't make the type completely specify a plug.
-- pIntertwine : {α : Set} {a b c d : ℕ} → ℂ α ((a + b) + (c + d)) ((a + c) + (b + d))
-- pIntertwine {_} {a} {b} {c} {d} = Plug pIntertwine'
--     where pIntertwine' : Fin ((a + c) + (b + d)) → Fin ((a + b) + (c + d))
--           pIntertwine' x rewrite sym (CS.+-assoc (a + b) c d)
--                                | CS.+-assoc a b c
--                                | CS.+-comm b c
--                                | sym (CS.+-assoc a c b)
--                                | CS.+-assoc (a + c) b d = x

-- -- vector plugs
-- pHead : {α : Set} {n : ℕ} → ℂ α (suc n) 1
-- pHead = Plug pHead'
--     where pHead' : {n : ℕ} → Fin 1 → Fin (suc n)
--           pHead' Fz = Fz
--           pHead' (Fs ())

-- pTail : {α : Set} {n : ℕ} → ℂ α (suc n) n
-- pTail = Plug pTail'
--     where pTail' : {n : ℕ} → Fin n → Fin (suc n)
--           pTail' x = Fs x

-- pUncons : {α : Set} {w n : ℕ} → ℂ α (suc n * w) (w + n * w)
-- pUncons {_} {w} {n} = Plug pUncons'
--     where pUncons' : Fin (w + n * w) → Fin (suc n * w)
--           pUncons' x = x

-- pCons : ∀ {α w n} → ℂ α (w + n * w) (suc n * w)
-- pCons {_} {w} {n} = Plug pCons'
--     where pCons' : Fin (suc n * w) → Fin (w + n * w)
--           pCons' x = x
