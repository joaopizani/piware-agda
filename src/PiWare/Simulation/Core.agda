module PiWare.Simulation.Core where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; [_]; _++_; splitAt; map; lookup; replicate)
                     renaming (_∷_ to _◁_; [] to ε)

open import Relation.Binary.PropositionalEquality using (refl)

open import PiWare.Circuit.Core
open import PiWare.Samples

open import Coinduction


data Stream (α : Set) : Set where
    _∷_ : (x : α) (xs : ∞ (Stream α)) → Stream α

streamMap : ∀ {α β} → (α → β) → Stream α → Stream β
streamMap f (x ∷ xs) = f x ∷ ♯ streamMap f (♭ xs)

streamRepeat : ∀ {α} → α → Stream α
streamRepeat x = x ∷ ♯ streamRepeat x


allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = ε
allFins {suc m} = Fz ◁ map Fs allFins

core⟦_⟧ : {i o : ℕ} → Coreℂ 𝔹 i o → (Vec 𝔹 i → Vec 𝔹 o)
core⟦ Not ⟧        (x ◁ ε)     = [ not x ]
core⟦ And ⟧        (x ◁ y ◁ ε) = [ x ∧ y ]
core⟦ Or  ⟧        (x ◁ y ◁ ε) = [ x ∨ y ]
core⟦ Plug p ⟧     v           = map (λ o → lookup (p o) v) allFins
core⟦ c₁ >> c₂ ⟧   v           = core⟦ c₂ ⟧ (core⟦ c₁ ⟧ v)
core⟦ _><_ {i₁} c₁ c₂ ⟧ v with splitAt i₁ v
core⟦ c₁ >< c₂ ⟧ .(v₁ ++ v₂) | v₁ , v₂ , refl = core⟦ c₁ ⟧ v₁ ++ core⟦ c₂ ⟧ v₂


stream⟦_⟧ : {i o : ℕ} → Streamℂ 𝔹 i o → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
stream⟦ Comb cc ⟧      = streamMap core⟦ cc ⟧
stream⟦ DelayLoop cc ⟧ = evalStreamAcc cc (replicate false)
    where evalStreamAcc : {i o l : ℕ} → Coreℂ 𝔹 (i + l) (o + l) → Vec 𝔹 l → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
          evalStreamAcc {o = o} cc acc (x ∷ xs) with splitAt o (core⟦ cc ⟧ (x ++ acc))
          ... | out , back , _ = out ∷ ♯ evalStreamAcc cc back (♭ xs)
