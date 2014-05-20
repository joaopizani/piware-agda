module PiWare.Atom.Bool where

open import Function using (id)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat using (s≤s; z≤n)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import PiWare.Atom

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
    enumerate𝔹 : Fin 2 → 𝔹
    enumerate𝔹 Fz      = false
    enumerate𝔹 (Fs Fz) = true
    enumerate𝔹 (Fs (Fs ()))

    atom#-inject-𝔹 : (x y : Fin 2) → enumerate𝔹 x ≡ enumerate𝔹 y → x ≡ y
    atom#-inject-𝔹 Fz           Fz           refl = refl
    atom#-inject-𝔹 (Fs Fz)      (Fs Fz)      refl = refl
    atom#-inject-𝔹 Fz           (Fs Fz)      ()
    atom#-inject-𝔹 (Fs Fz)      Fz           ()
    atom#-inject-𝔹 Fz           (Fs (Fs ())) _
    atom#-inject-𝔹 (Fs Fz)      (Fs (Fs ())) _
    atom#-inject-𝔹 (Fs (Fs ())) Fz           _
    atom#-inject-𝔹 (Fs (Fs ())) (Fs y)       _


Atom𝔹 : AtomInfo
Atom𝔹 = record {
      Atom = 𝔹
    ; card = 2
    ; atom# = enumerate𝔹
    ; 𝔹→atom = id
    ; atom→𝔹 = id
   
    ; card≥2 = s≤s (s≤s z≤n)
    ; inv-atom𝔹 = λ { true → refl ; false → refl }
    ; inj-atom# = atom#-inject-𝔹
    }
