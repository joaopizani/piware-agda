\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Correctness (At : Atomic) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; _++_; splitAt) renaming ([] to ε; _∷_ to _◁_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (map to mapₚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import PiWare.Synthesizable At
open ⇓W⇑ ⦃ ... ⦄

open import PiWare.Circuit.Core using (ℂ'; _⟫'_; _|'_; comb'; _comb⟫'_; _comb|'_)
open import PiWare.Circuit using (ℂ; Mkℂ; comb; _⟫_; _||_; _comb⟫_; _comb|_; comb|+)
open import PiWare.Simulation.Core using (⟦_⟧')
open import PiWare.Simulation using (⟦_⟧)
\end{code}


%<*seqproof-eq-core>
\AgdaTarget{\_⟫≡'\_}
\begin{code}
_⟫≡'_ :
    {i m o : ℕ} {f₁ : W i → W m} {f₂ : W m → W o} {gt : Gates At}
    {c₁ : ℂ' gt i m} {c₂ : ℂ' gt m o} {p₁ : comb' gt {i} {m} c₁} {p₂ : comb' gt {m} {o} c₂}
    → ((v₁ : W i) → ⟦_⟧' gt {i} {m} c₁ {p₁} v₁ ≡ f₁ v₁)
    → ((v₂ : W m) → ⟦_⟧' gt {m} {o} c₂ {p₂} v₂ ≡ f₂ v₂)
    → ((v : W i) → ⟦_⟧' gt {i} {o} (c₁ ⟫' c₂) {_comb⟫'_ gt {i} {m} {o} {c₁} {c₂} p₁ p₂} v ≡ (f₂ ∘ f₁) v)
_⟫≡'_ {f₁ = f₁} pc₁ pc₂ v rewrite sym (pc₂ (f₁ v)) | sym (pc₁ v) = refl
\end{code}
%</seqproof-eq-core>


\begin{code}
lemma-proj₁-splitAt : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂)
                      → proj₁ (splitAt i₁ (v₁ ++ v₂)) ≡ v₁
lemma-proj₁-splitAt {i₁ = zero}  ε        v₂ = refl
lemma-proj₁-splitAt {i₁ = suc n} (v ◁ vs) v₂ with splitAt n (vs ++ v₂) | lemma-proj₁-splitAt {i₁ = n} vs v₂
lemma-proj₁-splitAt {i₁ = suc n} (v ◁ vs) v₂ | _ , _ , eq | ind rewrite eq | ind = refl

lemma-proj₁₂-splitAt : ∀ {ℓ} {α : Set ℓ} {i₁ i₂} (v₁ : Vec α i₁) (v₂ : Vec α i₂) 
                       → proj₁ (proj₂ (splitAt i₁ (v₁ ++ v₂))) ≡ v₂
lemma-proj₁₂-splitAt {i₁ = zero}  ε        _  = refl
lemma-proj₁₂-splitAt {i₁ = suc n} (v ◁ vs) v₂ with splitAt n (vs ++ v₂) | lemma-proj₁₂-splitAt {i₁ = n} vs v₂
lemma-proj₁₂-splitAt {i₁ = suc n} (v ◁ vs) v₂ | _ , _ , eq | ind rewrite eq | ind = refl
\end{code}

%<*parproof-eq-core>
\AgdaTarget{\_|≡'\_}
\begin{code}
_|≡'_ :
    {i₁ o₁ i₂ o₂ : ℕ} {f₁ : W i₁ → W o₁} {f₂ : W i₂ → W o₂} {gt : Gates At}
    {c₁ : ℂ' gt i₁ o₁} {c₂ : ℂ' gt i₂ o₂} {p₁ : comb' gt {i₁} {o₁} c₁} {p₂ : comb' gt {i₂} {o₂} c₂}
    → ((v₁ : W i₁) → ⟦_⟧' gt {i₁} {o₁} c₁ {p₁} v₁ ≡ f₁ v₁)
    → ((v₂ : W i₂) → ⟦_⟧' gt {i₂} {o₂} c₂ {p₂} v₂ ≡ f₂ v₂)
    → ((v₁ : W i₁) (v₂ : W i₂)
        → ⟦_⟧' gt {i₁ + i₂} {o₁ + o₂} (c₁ |' c₂) {_comb|'_ gt {i₁} {o₁} {i₂} {o₂} {c₁} {c₂} p₁ p₂} (v₁ ++ v₂)
        ≡ f₁ v₁ ++ f₂ v₂
      )
_|≡'_ {i₁ = i₁} {f₁ = f₁} pc₁ pc₂ v₁ v₂
    rewrite lemma-proj₁-splitAt v₁ v₂
          | lemma-proj₁₂-splitAt v₁ v₂
          | pc₁ v₁
          | pc₂ v₂ = refl
\end{code}
%</parproof-eq-core>



%<*eq-down>
\AgdaTarget{eq⇓}
\begin{code}
eq⇓ :
    ∀ {α i β j} → {gt : Gates At} {c' : ℂ' gt i j} {f : W i → W j} {p : comb' gt c'}
    ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄
    → ((x : α) → ⟦_⟧ gt {α} {i} {β} {j} (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') {p} x ≡ ⇑ ⦃ sβ ⦄ (f (⇓ ⦃ sα ⦄ x)) )
    → ((v : W i) → ⟦_⟧' gt {i} {j} c' {p} v ≡ f v)
eq⇓ ⦃ sα = sα ⦄ p⇑ v rewrite (p⇑ (⇑ v)) = {!!}
\end{code}
%</eq-down>

%<*eq-up>
\AgdaTarget{eq⇑}
\begin{code}
eq⇑ :
    ∀ {α i β j} → {gt : Gates At} {c' : ℂ' gt i j} {f : W i → W j} {p : comb' gt c'}
    ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄
    → ((v : W i) → ⟦_⟧' gt {i} {j} c' {p} v ≡ f v)
    → ((x : α) → ⟦_⟧ gt {α} {i} {β} {j} (Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c') {p} x ≡ ⇑ ⦃ sβ ⦄ (f (⇓ ⦃ sα ⦄ x)) )
eq⇑ ⦃ sα ⦄ ⦃ sβ ⦄ p⇓ x rewrite p⇓ (⇓ x) = refl
\end{code}
%</eq-up>


%<*seqproof-eq>
\AgdaTarget{\_⟫≡\_}
\begin{code}
_⟫≡_ :
    ∀ {α i β j γ k} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ {f₁ : α → β} {f₂ : β → γ}
    → {gt : Gates At} {c₁ : ℂ gt α β {i} {j}} {c₂ : ℂ gt β γ {j} {k}} {p₁ : comb gt c₁} {p₂ : comb gt c₂}
    → ((x₁ : α) → ⟦_⟧ gt {α} {i} {β} {j} c₁ {p₁} x₁ ≡ f₁ x₁)
    → ((x₂ : β) → ⟦_⟧ gt {β} {j} {γ} {k} c₂ {p₂} x₂ ≡ f₂ x₂)
    → ((x : α)
        → ⟦_⟧ gt {α} {i} {γ} {k} (_⟫_ gt c₁ c₂)
          {_comb⟫_ gt {α} {i} {β} {j} {γ} {k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ {c₁} {c₂} p₁ p₂} x
        ≡ (f₂ ∘ f₁) x
      )
_⟫≡_ ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ {f₁ = f₁} {f₂ = f₂} {c₁ = Mkℂ c₁'} {c₂ = Mkℂ c₂'} pc₁ pc₂ x = {!!}
\end{code}
%</seqproof-eq>


%<*parproof-eq>
\AgdaTarget{\_|≡\_}
\begin{code}
_|≡_ :
    ∀ {α i β j γ k δ l} → ⦃ sα : ⇓W⇑ α {i} ⦄ ⦃ sβ : ⇓W⇑ β {j} ⦄ ⦃ sγ : ⇓W⇑ γ {k} ⦄ ⦃ sδ : ⇓W⇑ δ {l} ⦄
    → {f₁ : α → γ} {f₂ : β → δ} {gt : Gates At} {c₁ : ℂ gt α γ {i} {k}} {c₂ : ℂ gt β δ {j} {l}}
    → {p₁ : comb gt c₁} {p₂ : comb gt c₂} {x₁ : α} {x₂ : β}
    → ⟦_⟧ gt {i = i} {j = k} c₁ {p₁} x₁ ≡ f₁ x₁
    → ⟦_⟧ gt {i = j} {j = l} c₂ {p₂} x₂ ≡ f₂ x₂
    → ⟦_⟧ gt {i = i + j} {j = k + l} (_||_ gt c₁ c₂)
      {_comb|_ gt {α} {i} {γ} {k} {β} {j} {δ} {l} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ {c₁} {c₂} p₁ p₂} (x₁ , x₂)
      ≡ mapₚ f₁ f₂ (x₁ , x₂)
pc₁ |≡ pc₂ = {!!}
\end{code}
%</parproof-eq>
