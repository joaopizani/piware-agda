module PiWare.Plugs where

open import Function using (id)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)

open import PiWare.Wires
open import PiWare.Circuit


-- identity
pid : ∀ {α w} → ℂ α w w
pid = Plug id

-- forking
fork2 : ∀ {α w} → ℂ α w (w ⊞ w)
fork2 = Plug fork2′
    where fork2′ : ∀ {w} → ⟬ w ⊞ w ⟭ → ⟬ w ⟭
          fork2′ (inj₁ x) = x
          fork2′ (inj₂ y) = y


-- associativity plugs
pALR : ∀ {α w v y} → ℂ α ((w ⊞ v) ⊞ y) (w ⊞ (v ⊞ y))
pALR = Plug pALR′
    where pALR′ : ∀ {w v y} → ⟬ w ⊞ (v ⊞ y) ⟭ → ⟬ (w ⊞ v) ⊞ y ⟭
          pALR′ (inj₁ l)         = inj₁ (inj₁ l)
          pALR′ (inj₂ (inj₁ rl)) = inj₁ (inj₂ rl)
          pALR′ (inj₂ (inj₂ rr)) = inj₂ rr

pARL : ∀ {α w v y} → ℂ α (w ⊞ (v ⊞ y)) ((w ⊞ v) ⊞ y)
pARL = Plug pARL′
    where pARL′ : ∀ {w v y} → ⟬ (w ⊞ v) ⊞ y ⟭ → ⟬ w ⊞ (v ⊞ y) ⟭
          pARL′ (inj₁ (inj₁ ll)) = inj₁ ll
          pARL′ (inj₁ (inj₂ lr)) = inj₂ (inj₁ lr)
          pARL′ (inj₂ r)         = inj₂ (inj₂ r)

pSwap : ∀ {α w v} → ℂ α (w ⊞ v) (v ⊞ w)
pSwap = Plug pSwap'
    where pSwap' : ∀ {w v} → ⟬ v ⊞ w ⟭ → ⟬ w ⊞ v ⟭
          pSwap' (inj₁ x) = inj₂ x
          pSwap' (inj₂ x) = inj₁ x

pIntertwine : ∀ {α a b c d} → ℂ α ((a ⊞ b) ⊞ (c ⊞ d)) ((a ⊞ c) ⊞ (b ⊞ d))
pIntertwine = Plug pIntertwine'
    where pIntertwine' : ∀ {a b c d} → ⟬ (a ⊞ c) ⊞ (b ⊞ d) ⟭ → ⟬ (a ⊞ b) ⊞ (c ⊞ d) ⟭
          pIntertwine' (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
          pIntertwine' (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
          pIntertwine' (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
          pIntertwine' (inj₂ (inj₂ x)) = inj₂ (inj₂ x)

-- vector plugs
pHead : ∀ {α w n} → ℂ α (w ⊠ n) w
pHead = Plug pHead'
    where pHead' : ∀ {w n} → ⟬ w ⟭ → ⟬ w ⊠ n ⟭
          pHead' w' = Fz , w'

pTail : ∀ {α w n} → ℂ α (w ⊠ suc n) (w ⊠ n)
pTail = Plug pTail'
    where pTail' : ∀ {w n} → ⟬ w ⊠ n ⟭ → ⟬ w ⊠ suc n ⟭
          pTail' (i , w') = Fs i , w'

pUncons : ∀ {α w n} → ℂ α (w ⊠ suc n) (w ⊞  w ⊠ n)
pUncons = Plug pUncons'
    where pUncons' : ∀ {w n} → ⟬ w ⊞  w ⊠ n ⟭ → ⟬ w ⊠ suc n ⟭
          pUncons' (inj₁ w')       = Fz , w'
          pUncons' (inj₂ (i , v')) = Fs i , v'

pCons : ∀ {α w n} → ℂ α (w ⊞  w ⊠ n) (w ⊠ suc n)
pCons = Plug pCons'
    where pCons' : ∀ {w n} → ⟬ w ⊠ suc n ⟭ → ⟬ w ⊞  w ⊠ n ⟭
          pCons' (Fz , w')   = inj₁ w'
          pCons' (Fs i , w') = inj₂ (i , w')

pSingletonOut : ∀ {α w} → ℂ α (w ⊠ 0) w
pSingletonOut {α} {w} = pHead {α}

pSingletonIn : ∀ {α w} → ℂ α w (w ⊠ 0)
pSingletonIn = Plug pSingletonIn'
    where pSingletonIn' : ∀ {w} → ⟬ w ⊠ 0 ⟭ → ⟬ w ⟭
          pSingletonIn' (Fz    , w') = w'
          pSingletonIn' (Fs () , w')
