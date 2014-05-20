module PiWare.Simulation.Core where

open import Function using (_$_)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Vec using (Vec; [_]; _++_; splitAt; map; lookup; replicate) renaming (_∷_ to _◁_; [] to ε)

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Stream using (Stream; _∷_; zipWith; take) renaming (map to smap)
open import Coinduction

open import PiWare.Circuit.Core


-- helpers for circuit evaluation (both combinational and sequential)
allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

plugOutputs : {α : Set} {o i : ℕ} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = map (λ fin → lookup (p fin) ins) allFins


-- stream helpers for sequential circuit evaluation
fstHalfVecStream : {α : Set} {n m : ℕ} → Stream (Vec α (n + m)) → Stream (Vec α n)
fstHalfVecStream {n = k} (v ∷ vs) with splitAt k v
fstHalfVecStream (.(v₁ ++ v₂) ∷ vs) | v₁ , v₂ , refl = v₁ ∷ ♯ fstHalfVecStream (♭ vs)

sndHalfVecStream : {α : Set} {n m : ℕ} → Stream (Vec α (n + m)) → Stream (Vec α m)
sndHalfVecStream {_} {n} {_} (v ∷ vs) with splitAt n v
sndHalfVecStream {_} {n} {m} (.(v₁ ++ v₂) ∷ vs) | v₁ , v₂ , refl = v₂ ∷ ♯ sndHalfVecStream {_} {n} {m} (♭ vs)

splitVecStream : {α : Set} {n m : ℕ} → Stream (Vec α (n + m)) → Stream (Vec α n) × Stream (Vec α m)
splitVecStream {_} {n} {m} = < fstHalfVecStream , sndHalfVecStream {_} {n} {m} >

joinVecStream : {α : Set} {n m : ℕ} → Stream (Vec α n) × Stream (Vec α m) → Stream (Vec α (n + m))
joinVecStream (vs₁ , vs₂) = zipWith (_++_) vs₁ vs₂


-- combinational eval
⟦_⟧' : {i o : ℕ} → ℂ' 𝔹 i o → (Vec 𝔹 i → Vec 𝔹 o)
⟦ Not ⟧'      (x ◁ ε)     = [ not x ]
⟦ And ⟧'      (x ◁ y ◁ ε) = [ x ∧ y ]
⟦ Or  ⟧'      (x ◁ y ◁ ε) = [ x ∨ y ]
⟦ Plug p ⟧'   v           = plugOutputs p v
⟦ c₁ ⟫' c₂ ⟧' v           = ⟦ c₂ ⟧' (⟦ c₁ ⟧' v)
⟦ _|'_ {i₁} c₁ c₂ ⟧' v with splitAt i₁ v
⟦ c₁ |' c₂ ⟧' .(v₁ ++ v₂) | v₁ , v₂ , refl = ⟦ c₁ ⟧' v₁ ++ ⟦ c₂ ⟧' v₂

-- sequential eval (accumulating parameter)
⟦_⟧*'' : {i o l : ℕ} → ℂ' 𝔹 (i + l) (o + l) → Vec 𝔹 l → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ c ⟧*'' acc (x ∷ xs) with splitAt _ (⟦ c ⟧' (x ++ acc))
⟦ c ⟧*'' acc (x ∷ xs) | out , back , _ = out ∷ ♯ ⟦ c ⟧*'' back (♭ xs)

-- take 7 (⟦ sampleReg ⟧* (repeat (true , true)))

-- sequential eval
⟦_⟧*' : {i o : ℕ} → ℂ'* 𝔹 i o → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ Comb c      ⟧*' si = smap ⟦ c ⟧' si
⟦ DelayLoop c ⟧*' si = replicate false ∷ ♯ ⟦ c ⟧*'' (replicate false) si
⟦ Plug p      ⟧*' si = smap (plugOutputs p) si
⟦ c₁ ⟫'* c₂   ⟧*' si = ⟦ c₂ ⟧*' (⟦ c₁ ⟧*' si)
⟦ _|'*_ {i₁} c₁ c₂ ⟧*' si with splitVecStream {_} {i₁} si
⟦ c₁ |'* c₂ ⟧*' si | si₁ , si₂ = joinVecStream (⟦ c₁ ⟧*' si₁ , ⟦ c₂ ⟧*' si₂)
