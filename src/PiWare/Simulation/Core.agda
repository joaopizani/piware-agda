module PiWare.Simulation.Core where

open import Function using (_$_)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (not; _∧_; _∨_; false; true) renaming (Bool to 𝔹)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; [_]; _++_; splitAt; map; lookup; replicate)
                     renaming (_∷_ to _◁_; [] to ε)

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Stream using (Stream; _∷_) renaming (map to smap)
open import Coinduction

open import PiWare.Circuit.Core
open import PiWare.Samples


allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

⟦_⟧' : {i o : ℕ} → Combℂ 𝔹 i o → (Vec 𝔹 i → Vec 𝔹 o)
⟦ Not ⟧'        (x ◁ ε)     = [ not x ]
⟦ And ⟧'        (x ◁ y ◁ ε) = [ x ∧ y ]
⟦ Or  ⟧'        (x ◁ y ◁ ε) = [ x ∨ y ]
⟦ Plug p ⟧'     v           = map (λ o → lookup (p o) v) allFins
⟦ c₁ >> c₂ ⟧'   v           = ⟦ c₂ ⟧' (⟦ c₁ ⟧' v)
⟦ _><_ {i₁} c₁ c₂ ⟧' v with splitAt i₁ v
⟦ c₁ >< c₂ ⟧' .(v₁ ++ v₂) | v₁ , v₂ , refl = ⟦ c₁ ⟧' v₁ ++ ⟦ c₂ ⟧' v₂


⟦_⟧*' : {i o : ℕ} → Coreℂ 𝔹 i o → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ Comb c     ⟧*' si = smap ⟦ c ⟧' si
⟦ Delayed c ⟧*'  si = replicate false ∷ ♯ ⟦ c ⟧*'' (replicate false) si
    where ⟦_⟧*'' : {i o l : ℕ} → Combℂ 𝔹 (i + l) (o + l) → Vec 𝔹 l → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
          ⟦ c ⟧*'' acc (x ∷ xs) with splitAt _ (⟦ c ⟧' (x ++ acc))
          ⟦ c ⟧*'' acc (x ∷ xs) | out , back , _ = out ∷ ♯ ⟦ c ⟧*'' back (♭ xs)
