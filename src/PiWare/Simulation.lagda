\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Simulation {At : Atomic} (Gt : Gates At) where

open import Function using (_∘′_; flip)
open import Data.Nat.Base using (_+_)
open import Data.Fin using () renaming (zero to Fz)
open import Data.Product using (_,_; uncurry′) renaming (map to mapₚ)
open import Data.Stream using (Stream)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (_∷_) renaming (map to map⁺)
open import Data.CausalStream using (_⇒ᶜ_; runᶜ; pasts)
open import Data.Vec.Extra using (splitAt′)
open import Data.List.NonEmpty using (head)
open import Data.List.NonEmpty.Extra using (unzip⁺; splitAt⁺; uncurry⁺)
open import Data.Vec using (Vec; _++_; lookup; replicate; drop; tabulate) renaming ([] to ε; take to takeᵥ)

open Atomic At using (W; n→atom)
open Gates At Gt using (|in|; |out|; spec)
open import PiWare.Circuit Gt using (ℂ; σ)
open import PiWare.Circuit.Algebra Gt using (ℂσ★; cataℂσ; ℂ★; cataℂ; TyGate★; TyPlug★; Ty⟫★; Ty∥★)
\end{code}


%<*Word-function>
\AgdaTarget{W⟶W}
\begin{code}
W⟶W : ∀ m n → Set
W⟶W m n = W m → W n
\end{code}
%</Word-function>

%<*combinator-Word-function-types>
\begin{code}
gate     : TyGate★ W⟶W
plug     : TyPlug★ W⟶W
seq-comb : Ty⟫★ W⟶W
par-comb : Ty∥★ W⟶W
\end{code}
%</combinator-Word-function-types>

%<*combinator-Word-function-defs>
\AgdaTarget{nil,gate,plug,seq-comb,par-comb,sum-comb}
\begin{code}
gate                = spec
plug p ins          = tabulate (flip lookup ins ∘′ flip lookup p)
seq-comb            = flip _∘′_
par-comb {i₁} f₁ f₂ = uncurry′ _++_ ∘′ mapₚ f₁ f₂ ∘′ splitAt′ i₁
\end{code}
%</combinator-Word-function-defs>

%<*simulation-combinational-algebra>
\AgdaTarget{simulation-combinational}
\begin{code}
simulation-combinational : ℂσ★ {W⟶W}
simulation-combinational = record { Gate★ = gate;  Plug★ = plug;  _⟫★_ = seq-comb;  _∥★_ = par-comb }
\end{code}
%</simulation-combinational-algebra>

%<*simulation-combinational>
\AgdaTarget{⟦\_⟧}
\begin{code}
⟦_⟧ : ∀ {i o} → ℂ i o → W⟶W i o
⟦_⟧ = cataℂσ simulation-combinational
\end{code}
%</simulation-combinational>



%<*Word-causal-function>
\AgdaTarget{W⇒ᶜW}
\begin{code}
W⇒ᶜW : ∀ i o → Set
W⇒ᶜW i o = W i ⇒ᶜ W o
\end{code}
%</Word-causal-function>

-- TODO: Now it's hardcoded to pad the sequence with th first element being (replicate (n→atom Fz))
-- TODO: memoize this
%<*delay>
\AgdaTarget{delay}
\begin{code}
delay : ∀ o {i l} → W⟶W (i + l) (o + l) → W⇒ᶜW i (o + l)
delay o {i} {l} = uncurry⁺ ∘′ delay′ o {i} {l}
  where delay′ : ∀ o {i l} → W⟶W (i + l) (o + l) → W i → List (W i) → W (o + l)
        delay′ _ f w⁰ []         = f (w⁰ ++ replicate (n→atom Fz))
        delay′ o f w⁰ (w⁻¹ ∷ w⁻) = f (w⁰ ++ drop o (delay′ o f w⁻¹ w⁻))
\end{code}
%</delay>

%<*delay-seq>
\AgdaTarget{delay-seq}
\begin{code}
delay-seq : ∀ {i o l} → W⟶W (i + l) (o + l) → W⇒ᶜW i o
delay-seq {_} {o} f = takeᵥ o ∘′ delay o f
\end{code}
%</delay-seq>

%<*combinator-word-causal-function-types>
\begin{code}
seq-seq : Ty⟫★ W⇒ᶜW
par-seq : Ty∥★ W⇒ᶜW
\end{code}
%</combinator-word-causal-function-types>

%<*combinator-word-causal-function-defs>
\AgdaTarget{seq-seq,par-seq,sum-seq}
\begin{code}
seq-seq      f₁ f₂ = f₂ ∘′ map⁺ f₁ ∘′ pasts
par-seq {i₁} f₁ f₂ = uncurry′ _++_ ∘′ mapₚ f₁ f₂ ∘′ unzip⁺ ∘′ splitAt⁺ i₁
\end{code}
%</combinator-word-causal-function-defs>

%<*simulation-causal-algebra>
\AgdaTarget{simulation-sequential}
\begin{code}
simulation-sequential : ℂ★ {W⟶W} {W⇒ᶜW}
simulation-sequential = record { Gate★ = λ g → gate g ∘′ head; Plug★ = λ f → plug f ∘′ head; _⟫★_ = seq-seq; _∥★_ = par-seq; DelayLoop★ = delay-seq}
\end{code}
%</simulation-causal-algebra>

%<*simulation-causal>
\AgdaTarget{⟦\_⟧ᶜ}
\begin{code}
⟦_⟧ᶜ : ∀ {i o} → ℂ i o → (W i ⇒ᶜ W o)
⟦_⟧ᶜ = cataℂ simulation-combinational simulation-sequential
\end{code}
%</simulation-causal>

%<*simulation-sequential>
\AgdaTarget{⟦\_⟧*}
\begin{code}
⟦_⟧ω : ∀ {i o} → ℂ i o → (Stream (W i) → Stream (W o))
⟦_⟧ω = runᶜ ∘′ ⟦_⟧ᶜ
\end{code}
%</simulation-sequential>
