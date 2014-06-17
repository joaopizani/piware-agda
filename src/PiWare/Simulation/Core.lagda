\begin{code}
module PiWare.Simulation.Core where

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (not; _∧_; _∨_; false) renaming (Bool to 𝔹)
open import Data.Product using (_×_; _,_; <_,_>; uncurry′)
open import Data.Sum using (_⊎_)
open import Data.Vec using (Vec; _++_; splitAt; lookup; replicate; allFin)
                     renaming (_∷_ to _◁_; take to takeᵥ; drop to dropᵥ; map to mapᵥ; [_] to [_]ᵥ)
open import Data.Stream using (Stream; _∷_; zipWith; take) renaming (map to mapₛ)

open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Coinduction using (♯_; ♭)

-- TODO: Now hardcoded to Atom𝔹, generalize later
open import PiWare.Atom
open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Padding using (unpadFst; unpadSnd)
open import PiWare.Circuit.Core
open AtomInfo Atom𝔹

open import Data.List using (List; []; _∷_; [_]; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺; [_] to [_]⁺)
\end{code}


-- helpers for circuit evaluation (both combinational and sequential)
%<*plugOutputs>
\begin{code}
plugOutputs : {α : Set} {o i : ℕ} → (Fin o → Fin i) → Vec α i → Vec α o
plugOutputs p ins = mapᵥ (λ fin → lookup (p fin) ins) (allFin _)
\end{code}
%</plugOutputs>

%<*fstVec*>
\begin{code}
fstVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α n)
fstVec* {n = k} (v ∷ vs) with splitAt k v
fstVec* (.(w ++ y) ∷ vs) | w , y , refl = w ∷ ♯ fstVec* (♭ vs)
\end{code}
%</fstVec*>

%<*sndVec*>
\begin{code}
sndVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α m)
sndVec* {_} {n} {_} (v ∷ vs) with splitAt n v
sndVec* {_} {n} {m} (.(w ++ y) ∷ vs) | w , y , refl = y ∷ ♯ sndVec* {_} {n} {m} (♭ vs)
\end{code}
%</sndVec*>

%<*splitVec*>
\begin{code}
splitVec* : ∀ {α n m} → Stream (Vec α (n + m)) → Stream (Vec α n) × Stream (Vec α m)
splitVec* {_} {n} {m} = < fstVec* , sndVec* {_} {n} {m} >
\end{code}
%</splitVec*>

\begin{code}
splitVecₗ : {α : Set} (n m : ℕ) → List (Vec α (n + m)) → List (Vec α n) × List (Vec α m)
splitVecₗ _ _ [] = [] , []
splitVecₗ n m (v ∷ vs)           with splitAt n v | splitVecₗ n m vs
splitVecₗ n m (.(v₁ ++ v₂) ∷ vs) | v₁ , v₂ , refl | vs₁ , vs₂ = v₁ ∷ vs₁ , v₂ ∷ vs₂
\end{code}

%<*joinVec*>
\begin{code}
joinVec* : {α : Set} {n m : ℕ} → Stream (Vec α n) × Stream (Vec α m) → Stream (Vec α (n + m))
joinVec* (vs₁ , vs₂) = zipWith (_++_) vs₁ vs₂
\end{code}
%</joinVec*>


-- combinational eval
%<*eval'>
\begin{code}
⟦_⟧' : {i o : ℕ} → (c : ℂ' Atom𝔹 i o) {p : comb' c} → (Vec 𝔹 i → Vec 𝔹 o)
⟦ Not ⟧' (x ◁ ε)     = [ not x ]ᵥ
⟦ And ⟧' (x ◁ y ◁ ε) = [ x ∧ y ]ᵥ
⟦ Or  ⟧' (x ◁ y ◁ ε) = [ x ∨ y ]ᵥ
⟦ Plug p   ⟧' v = plugOutputs p v
⟦ c₁ ⟫' c₂  ⟧' {p = (p₁ , p₂)} v = ⟦ c₂ ⟧' {p = p₂} (⟦ c₁ ⟧' {p = p₁} v)
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} v with splitAt i₁ v
⟦ _|'_ {i₁} c₁ c₂  ⟧' {p = (p₁ , p₂)} .(v₁ ++ v₂) | v₁ , v₂ , refl = ⟦ c₁ ⟧' {p = p₁} v₁ ++ ⟦ c₂ ⟧' {p = p₂} v₂
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} (t ◁ ab) with toℕ (atom→n t) ≟ 1
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} (t ◁ ab) | yes _ = ⟦ c₂ ⟧' {p = p₂} (unpadSnd i₁ i₂ ab)
⟦ _|+'_ {i₁} {i₂} c₁ c₂ ⟧' {p = (p₁ , p₂)} (t ◁ ab) | no  _ = ⟦ c₁ ⟧' {p = p₁} (unpadFst i₁ i₂ ab)
⟦ DelayLoop c ⟧' {()} v
\end{code}
%</eval'>

sequential eval (accumulating parameter)
%<*eval*''>
\begin{code}
⟦_⟧*'' : {i o l : ℕ} → (c : ℂ' Atom𝔹 (i + l) (o + l)) {p : comb' c} → Vec 𝔹 l → Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o)
⟦ c ⟧*'' {p = p} acc (x ∷ xs) with splitAt _ (⟦ c ⟧' (x ++ acc))
⟦ c ⟧*'' {p = p} acc (x ∷ xs) | out , back , _ = out ∷ ♯ ⟦ c ⟧*'' {p = p} back (♭ xs)
\end{code}
%</eval*''>

-- sequential eval
%<*eval*'>
\begin{code}
⟦_⟧*' : {i o : ℕ} → ℂ' Atom𝔹 i o → (Stream (Vec 𝔹 i) → Stream (Vec 𝔹 o))
⟦ Not ⟧*' si = mapₛ ⟦ Not ⟧' si
⟦ And ⟧*' si = mapₛ ⟦ And ⟧' si
⟦ Or  ⟧*' si = mapₛ ⟦ Or ⟧' si
⟦ Plug p      ⟧*' si = mapₛ (plugOutputs p) si
⟦ DelayLoop c {p = p} ⟧*' si = replicate false ∷ ♯ ⟦ c ⟧*'' {p = p} (replicate false) si
⟦ c₁ ⟫'  c₂   ⟧*' si = ⟦ c₂ ⟧*' (⟦ c₁ ⟧*' si)
⟦ _|'_ {i₁} c₁ c₂ ⟧*' si with splitVec* {_} {i₁} si 
⟦ _|'_ {i₁} c₁ c₂ ⟧*' si | si₁ , si₂ = joinVec* (⟦ c₁ ⟧*' si₁ , ⟦ c₂ ⟧*' si₂)
⟦ c₁ |+' c₂   ⟧*' si = {!!} 
\end{code}
%</eval*'>

-- sequential eval as "causal stream function"
%<*eval*'-causal>
\begin{code}
-- Causal context: past × present
Γᶜ : (α : Set) → Set
Γᶜ = List⁺

-- Needs to use the trick trick with tails' and uncurry to "convince" the termination checker
tails : ∀ {α} → Γᶜ α → List⁺ (List⁺ α)
tails {α} = uncurry′ tails'
    where tails' : α → List α → List⁺ (List⁺ α)
          tails' x₀ []        = [ x₀ , [] ]⁺
          tails' x₀ (x₁ ∷ xs) = let (t₁ ∷ ts) = tails' x₁ xs  in  t₁ , ts

-- Causal stream step: causal context → next future value
_⇒ᶜ_ : (α β : Set) → Set
α ⇒ᶜ β = Γᶜ α → β

-- HERE, (⟦ c ⟧' {p} (i⁰ ++ l⁻¹)), in the time difference between i⁰ and l⁻¹, resides the delay!
delay : {#i #o #l : ℕ} (c : ℂ' Atom𝔹 (#i + #l) (#o + #l)) {p : comb' c} → Vec 𝔹 #i → List (Vec 𝔹 #i) → Vec 𝔹 (#o + #l)
delay {_} {_ } c {p} i⁰ []                       = ⟦ c ⟧' {p} (i⁰ ++ replicate false)
delay {_} {#o} c {p} i⁰ (i⁻¹ ∷ i⁻) with splitAt #o (delay {_} {#o} c {p} i⁻¹ i⁻)
delay {_} {#o} c {p} i⁰ (i⁻¹ ∷ i⁻) | _ , l⁻¹ , _ = ⟦ c ⟧' {p} (i⁰ ++ l⁻¹)


⟦_⟧ᶜ : {#i #o : ℕ} → ℂ' Atom𝔹 #i #o → (Vec 𝔹 #i ⇒ᶜ Vec 𝔹 #o)
⟦ Not         ⟧ᶜ (i⁰ ∷ _) = ⟦ Not ⟧' i⁰ 
⟦ And         ⟧ᶜ (i⁰ ∷ _) = ⟦ And ⟧' i⁰
⟦ Or          ⟧ᶜ (i⁰ ∷ _) = ⟦ Or  ⟧' i⁰
⟦ Plug p      ⟧ᶜ (i⁰ ∷ _) = plugOutputs p i⁰

⟦ DelayLoop {o = #o} c {p} ⟧ᶜ (i⁰ ∷ i⁻) = takeᵥ #o (delay {#o = #o} c {p} i⁰ i⁻)

⟦ c₁ ⟫' c₂    ⟧ᶜ is = ⟦ c₂ ⟧ᶜ (map⁺ ⟦ c₁ ⟧ᶜ (tails is))

⟦ _|'_ {#i₁} c₁ c₂ ⟧ᶜ (i⁰ ∷ i⁻) with splitAt #i₁ i⁰ | splitVecₗ #i₁ _ i⁻
⟦ _|'_ {#i₁} c₁ c₂ ⟧ᶜ (.(i⁰₁ ++ i⁰₂) ∷ i⁻) | i⁰₁ , i⁰₂ , refl | i⁻₁ , i⁻₂ = ⟦ c₁ ⟧ᶜ (i⁰₁ ∷ i⁻₁) ++ ⟦ c₂ ⟧ᶜ (i⁰₂ ∷ i⁻₂)

⟦ c₁ |+' c₂   ⟧ᶜ (i⁰ ∷ i⁻) = {!!}
\end{code}
