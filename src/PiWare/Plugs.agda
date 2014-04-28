module PiWare.Plugs where

open import Function using (id; _$_)
open import Data.Nat using (ℕ; _+_; suc; zero; _*_)
open import Data.Nat.DivMod using (DivMod; _divMod_)
open import Data.Fin using (Fin; toℕ) renaming (zero to Fz; suc to Fs)
open import Relation.Binary.PropositionalEquality using (sym)

open import PiWare.Circuit 


-- identity
pid : ∀ {α w} → ℂ α w w
pid = Plug id

-- forking
fork2 : {α : Set} {w : ℕ} → ℂ α w (w + w)
fork2 = Plug fork2′
    where fork2′ : {w : ℕ} → Fin (w + w) → Fin w
          fork2′ {zero}   ()
          fork2′ {suc w'} x = DivMod.remainder $ (toℕ x) divMod (suc w')


open import Algebra
import Data.Nat.Properties as Nat
private
    module CS = CommutativeSemiring Nat.commutativeSemiring

-- associativity and commutativity plugs
pALR : {α : Set} {w v y : ℕ} → ℂ α ((w + v) + y) (w + (v + y))
pALR {_} {w} {v} {y} = Plug pALR′
    where pALR′ : Fin (w + (v + y)) → Fin ((w + v) + y)
          pALR′ x rewrite CS.+-assoc w v y = x

pARL : {α : Set} {w v y : ℕ} → ℂ α (w + (v + y)) ((w + v) + y)
pARL {_} {w} {v} {y} = Plug pARL′
    where pARL′ : Fin ((w + v) + y) → Fin (w + (v + y))
          pARL′ x rewrite CS.+-assoc w v y = x


pComm : {α : Set} {w v : ℕ} → ℂ α (w + v) (v + w)
pComm {_} {w} {v} = Plug pComm'
    where pComm' : Fin (v + w) → Fin (w + v)
          pComm' x rewrite CS.+-comm w v = x

pIntertwine : {α : Set} {a b c d : ℕ} → ℂ α ((a + b) + (c + d)) ((a + c) + (b + d))
pIntertwine {_} {a} {b} {c} {d} = Plug pIntertwine'
    where pIntertwine' : Fin ((a + c) + (b + d)) → Fin ((a + b) + (c + d))
          pIntertwine' x rewrite sym (CS.+-assoc (a + b) c d)
                               | CS.+-assoc a b c
                               | CS.+-comm b c
                               | sym (CS.+-assoc a c b)
                               | CS.+-assoc (a + c) b d = x

-- vector plugs
pHead : {α : Set} {n : ℕ} → ℂ α (suc n) 1
pHead = Plug pHead'
    where pHead' : {n : ℕ} → Fin 1 → Fin (suc n)
          pHead' Fz = Fz
          pHead' (Fs ())

pTail : {α : Set} {n : ℕ} → ℂ α (suc n) n
pTail = Plug pTail'
    where pTail' : {n : ℕ} → Fin n → Fin (suc n)
          pTail' x = Fs x

pUncons : {α : Set} {w n : ℕ} → ℂ α (suc n * w) (w + n * w)
pUncons {_} {w} {n} = Plug pUncons'
    where pUncons' : Fin (w + n * w) → Fin (suc n * w)
          pUncons' x = x

pCons : ∀ {α w n} → ℂ α (w + n * w) (suc n * w)
pCons {_} {w} {n} = Plug pCons'
    where pCons' : Fin (suc n * w) → Fin (w + n * w)
          pCons' x = x
