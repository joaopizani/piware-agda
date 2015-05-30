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

open import Function.Bijection.Sets using (module Inverse′)
open Inverse′ using (to)

open Atomic At using (W; enum)
open Gates At Gt using (|in|; |out|; spec)
open import PiWare.Circuit {Gt = Gt} using (ℂ; σ)
open import PiWare.Circuit.Algebra {Gt = Gt} using (ℂσ★; cataℂσ; ℂ★; cataℂ; TyGate★; TyPlug★; Ty⟫★; Ty∥★)
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
gateσ  : TyGate★ W⟶W
plugσ  : TyPlug★ W⟶W
seqσ   : Ty⟫★    W⟶W
parσ   : Ty∥★    W⟶W
\end{code}
%</combinator-Word-function-types>

%<*combinator-Word-function-defs>
\AgdaTarget{gateσ,plugσ,seqσ,parσ}
\begin{code}
gateσ        = spec
plugσ p ins  = tabulate (flip lookup ins ∘′ flip lookup p)
seqσ         = flip _∘′_
parσ f₁ f₂   = uncurry′ _++_ ∘′ mapₚ f₁ f₂ ∘′ splitAt′ _
\end{code}
%</combinator-Word-function-defs>

%<*simulation-sigma-algebra>
\AgdaTarget{simulationσ}
\begin{code}
simulationσ : ℂσ★ {W⟶W}
simulationσ = record { Gate★ = gateσ;  Plug★ = plugσ;  _⟫★_ = seqσ;  _∥★_ = parσ }
\end{code}
%</simulation-sigma-algebra>

%<*simulation-combinational>
\AgdaTarget{⟦\_⟧}
\begin{code}
⟦_⟧ : ∀ {i o} → ℂ i o → W⟶W i o
⟦_⟧ = cataℂσ simulationσ
\end{code}
%</simulation-combinational>



%<*Word-causal-function>
\AgdaTarget{W⇒ᶜW}
\begin{code}
W⇒ᶜW : ∀ i o → Set
W⇒ᶜW i o = W i ⇒ᶜ W o
\end{code}
%</Word-causal-function>

-- TODO: Now it's hardcoded to pad the sequence with the first element being: replicate (n→atom Fz)
-- TODO: memoize this
%<*delay>
\AgdaTarget{delay}
\begin{code}
delay : ∀ o {i l} → W⟶W (i + l) (o + l) → W⇒ᶜW i (o + l)
delay o {i} {l} = uncurry⁺ ∘′ delay′ o {i} {l}
  where delay′ : ∀ o {i l} → W⟶W (i + l) (o + l) → W i → List (W i) → W (o + l)
        delay′ _ f w⁰ []         = f (w⁰ ++ replicate (to enum Fz))
        delay′ o f w⁰ (w⁻¹ ∷ w⁻) = f (w⁰ ++ drop o (delay′ o f w⁻¹ w⁻))
\end{code}
%</delay>

%<*delay-causal>
\AgdaTarget{delayᶜ}
\begin{code}
delayᶜ : ∀ {i o l} → W⟶W (i + l) (o + l) → W⇒ᶜW i o
delayᶜ {_} {o} f = takeᵥ o ∘′ delay o f
\end{code}
%</delay-causal>

%<*combinator-causal-function-types>
\begin{code}
gateᶜ : TyGate★ W⇒ᶜW
plugᶜ : TyPlug★ W⇒ᶜW
seqᶜ  : Ty⟫★    W⇒ᶜW
parᶜ  : Ty∥★    W⇒ᶜW
\end{code}
%</combinator-causal-function-types>

%<*combinator-causal-function-defs>
\AgdaTarget{seqω,parω}
\begin{code}
gateᶜ g     = gateσ g ∘′ head
plugᶜ f     = plugσ f ∘′ head
seqᶜ f₁ f₂  = f₂ ∘′ map⁺ f₁ ∘′ pasts
parᶜ f₁ f₂  = uncurry′ _++_ ∘′ mapₚ f₁ f₂ ∘′ unzip⁺ ∘′ splitAt⁺ _
\end{code}
%</combinator-causal-function-defs>

%<*simulation-causal-algebra>
\AgdaTarget{simulationᶜ}
\begin{code}
simulationᶜ : ℂ★ {W⟶W} {W⇒ᶜW}
simulationᶜ = record { Gate★ = gateᶜ;  Plug★ = plugᶜ;  _⟫★_ = seqᶜ;  _∥★_ = parᶜ;  DelayLoop★ = delayᶜ}
\end{code}
%</simulation-causal-algebra>

%<*simulation-causal>
\AgdaTarget{⟦\_⟧ᶜ}
\begin{code}
⟦_⟧ᶜ : ∀ {i o} → ℂ i o → (W i ⇒ᶜ W o)
⟦_⟧ᶜ = cataℂ {Aℓσ = simulationσ} simulationᶜ
\end{code}
%</simulation-causal>

%<*simulation-sequential>
\AgdaTarget{⟦\_⟧*}
\begin{code}
⟦_⟧ω : ∀ {i o} → ℂ i o → (Stream (W i) → Stream (W o))
⟦_⟧ω = runᶜ ∘′ ⟦_⟧ᶜ
\end{code}
%</simulation-sequential>
