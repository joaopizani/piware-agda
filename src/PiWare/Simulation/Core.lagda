\begin{code}
module PiWare.Simulation.Core where

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Sum using (_⊎_)
open import Data.Vec using (Vec; [_]; _++_; splitAt; map; lookup; replicate; allFin) renaming (_∷_ to _◁_)
open import Data.Stream using (Stream; _∷_; zipWith; take) renaming (map to smap)

open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

-- TODO: Now hardcoded to Atom𝔹, generalize later
open import PiWare.Atom
open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Padding using (unpadFst; unpadSnd)
open import PiWare.Circuit.Core
open AtomInfo Atom𝔹
\end{code}


-- helpers for circuit evaluation (both combinational and sequential)
\begin{code}
plugOutputs : {α : Set} {o i : ℕ} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = map (λ fin → lookup (p fin) ins) (allFin _)
\end{code}

\begin{code}
fstVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α n)
fstVec* {n = k} (v ∷ vs) with splitAt k v
fstVec* (.(w ++ y) ∷ vs) | w , y , refl = w ∷ ♯ fstVec* (♭ vs)
\end{code}

\begin{code}
sndVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α m)
sndVec* {_} {n} {_} (v ∷ vs) with splitAt n v
sndVec* {_} {n} {m} (.(w ++ y) ∷ vs) | w , y , refl = y ∷ ♯ sndVec* {_} {n} {m} (♭ vs)
\end{code}

\begin{code}
splitVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α n) × Stream (Vec α m)
splitVec* {_} {n} {m} = < fstVec* , sndVec* {_} {n} {m} >
\end{code}

\begin{code}
joinVec* : {α : Set} {n m : ℕ} → Stream (Vec α n) × Stream (Vec α m) → Stream (Vec α (n + m))
joinVec* (vs₁ , vs₂) = zipWith (_++_) vs₁ vs₂
\end{code}


-- combinational eval
\begin{code}
⟦_⟧' : {i o : ℕ} → ℂ' Atom𝔹 i o → (Vec 𝔹 i → Vec 𝔹 o)
⟦ Not ⟧'      (x ◁ ε)     = [ not x ]
⟦ And ⟧'      (x ◁ y ◁ ε) = [ x ∧ y ]
⟦ Or  ⟧'      (x ◁ y ◁ ε) = [ x ∨ y ]
⟦ Plug p ⟧'   v           = plugOutputs p v
⟦ c₁ ⟫' c₂ ⟧' v           = ⟦ c₂ ⟧' (⟦ c₁ ⟧' v)
⟦ _|'_ {i₁} c₁ c₂ ⟧' v with splitAt i₁ v
⟦ c₁ |' c₂ ⟧' .(v₁ ++ v₂) | v₁ , v₂  , refl = ⟦ c₁ ⟧' v₁ ++ ⟦ c₂ ⟧' v₂
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' (t ◁ ab) with toℕ (atom→n t) ≟ 1
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' (t ◁ ab) | yes _ = ⟦ c₂ ⟧' (unpadSnd i₁ i₂ ab)
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' (t ◁ ab) | no  _ = ⟦ c₁ ⟧' (unpadFst i₁ i₂ ab)
\end{code}

-- sequential eval (accumulating parameter)
\begin{code}
⟦_⟧*'' : {i o l : ℕ} → ℂ' Atom𝔹 (i + l) (o + l) → Vec 𝔹 l → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ c ⟧*'' acc (x ∷ xs) with splitAt _ (⟦ c ⟧' (x ++ acc))
⟦ c ⟧*'' acc (x ∷ xs) | out , back , _ = out ∷ ♯ ⟦ c ⟧*'' back (♭ xs)
\end{code}

-- sequential eval
\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ*' Atom𝔹 i o → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ Comb c      ⟧*' si = smap ⟦ c ⟧' si
⟦ DelayLoop c ⟧*' si = replicate false ∷ ♯ ⟦ c ⟧*'' (replicate false) si
⟦ Plug p      ⟧*' si = smap (plugOutputs p) si
⟦ c₁ ⟫*' c₂   ⟧*' si = ⟦ c₂ ⟧*' (⟦ c₁ ⟧*' si)
⟦ _|*'_ {i₁} c₁ c₂ ⟧*' si with splitVec* {_} {i₁} si
⟦ c₁ |*' c₂ ⟧*' si | si₁ , si₂ = joinVec* (⟦ c₁ ⟧*' si₁ , ⟦ c₂ ⟧*' si₂)
⟦ _|+*'_ {i₁} {i₂} c₁ c₂ ⟧*' ((t ◁ ab) ∷ abs) = {!!}
\end{code}
