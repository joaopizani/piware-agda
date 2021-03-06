\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates; module Gates)

module PiWare.Circuit.Typed {At : Atomic} (Gt : Gates At) where

open import Data.Nat.Base using (_+_)
open import Data.Product using (_×_)

open import PiWare.Interface using (Ix)
open import PiWare.Plugs.Core using (_⤪_)
open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×)
import PiWare.Circuit as Circuit
open Circuit {Gt = Gt} using (ℂ; IsComb; Gate; Plug; DelayLoop; _⟫_; _∥_)
open Circuit {Gt = Gt} using (σ; ω) public

open Gates At Gt using (|in|; |out|)
\end{code}


-- "High-level" circuit types, packing the synthesizable instances
%<*Circuit-typed>
\AgdaTarget{ℂ}
\begin{code}
record ℂ̂ {𝐜 : IsComb} (α β : Set) {i j : Ix} : Set where
    constructor Mkℂ̂
    field ⦃ sα ⦄ : ⇓W⇑ α {i}
          ⦃ sβ ⦄ : ⇓W⇑ β {j}
          base : ℂ {𝐜} i j
\end{code}
%</Circuit-typed>

%<*Circuit-any-typed>
\AgdaTarget{𝐂̂}
\begin{code}
𝐂̂ : (α β : Set) {i j : Ix} → Set
𝐂̂ α β {i} {j} = ∀ {𝐜} → ℂ̂ {𝐜} α β {i} {j}
\end{code}
%</Circuit-any-typed>


-- "Smart constructors"
%<*gateC>
\AgdaTarget{gateℂ̂}
\begin{code}
gateℂ̂ : ∀ g {α β} ⦃ _ : ⇓W⇑ α {|in| g} ⦄ ⦃ _ : ⇓W⇑ β {|out| g} ⦄ → 𝐂̂ α β
gateℂ̂ g ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ (Gate g)
\end{code}
%</gateC>


%<*plugC>
\AgdaTarget{plugℂ̂}
\begin{code}
plugℂ̂ : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → i ⤪ j → 𝐂̂ α β {i} {j}
plugℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ f = Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ (Plug f)
\end{code}
%</plugC>


%<*delayC>
\AgdaTarget{delayℂ̂}
\begin{code}
delayℂ̂ : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
         → ℂ̂ {σ} (α × γ) (β × γ) {i + k} {j + k} → ℂ̂ {ω} α β {i} {j}
delayℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ (Mkℂ̂ c) = Mkℂ̂ ⦃ sα ⦄ ⦃ sβ ⦄ (DelayLoop c)
\end{code}
%</delayC>


%<*seq>
\AgdaTarget{\_⟫̂\_}
\begin{code}
_⟫̂_ : ∀ {α i β j γ k 𝐜} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄
      → ℂ̂ {𝐜} α β {i} {j} → ℂ̂ {𝐜} β γ {j} {k} → ℂ̂ {𝐜} α γ {i} {k}
_⟫̂_ ⦃ sα ⦄ ⦃ _ ⦄ ⦃ sγ ⦄ (Mkℂ̂ c₁) (Mkℂ̂ c₂) = Mkℂ̂ ⦃ sα ⦄ ⦃ sγ ⦄ (c₁ ⟫ c₂)
\end{code}
%</seq>


%<*par>
\AgdaTarget{\_∥̂\_}
\begin{code}
_∥̂_ : ∀ {α i γ k β j δ l 𝐜} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ δ {l} ⦄
       → ℂ̂ {𝐜} α γ {i} {k} → ℂ̂ {𝐜} β δ {j} {l} → ℂ̂ {𝐜} (α × β) (γ × δ) {i + j} {k + l}
_∥̂_ ⦃ sα ⦄ ⦃ sγ ⦄ ⦃ sβ ⦄ ⦃ sδ ⦄ (Mkℂ̂ c₁) (Mkℂ̂ c₂) = Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ (c₁ ∥ c₂)
\end{code}
%</par>


\begin{code}
infixr 9 _∥̂_
infixl 8 _⟫̂_
\end{code}
