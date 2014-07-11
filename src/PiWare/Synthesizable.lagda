\begin{code}
open import PiWare.Atom

module PiWare.Synthesizable (At : Atomic) where

open import Function using (_∘_; _$_; const)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map⊎)
open import Data.Fin using (Fin; toℕ) renaming (zero to Fz; suc to Fs)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≟_; _⊔_)
open import Data.Vec using (Vec; _++_; splitAt; _>>=_; group) renaming (_∷_ to _◁_; [] to ε; map to mapᵥ)
open import Data.List using (List) renaming (map to mapₗ)

open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary.Core using (yes; no)

open import PiWare.Padding using (padFst; unpadFst; padSnd; unpadSnd)
open import PiWare.Utils using (segregateSums)
open Atomic At using (Atom; Atom#; atom→n; n→atom)
\end{code}


-- Words are sequences of "Atoms"
%<*Word>
\begin{code}
W : ℕ → Set
W = Vec Atom
\end{code}
%</Word>


-- Provides a mapping between "high-level" metalanguage types and words
-- TODO: proofs that ⇑ and ⇓ are inverses
%<*Synth>
\begin{code}
record ⇓W⇑ (α : Set) {i : ℕ} : Set where
    constructor ⇓W⇑[_,_]
    field
        ⇓ : α → W i
        ⇑ : W i → α
\end{code}
%</Synth>

\begin{code}
open ⇓W⇑ ⦃ ... ⦄
\end{code}


-- basic instances
%<*Synth-Unit>
\begin{code}
⇓W⇑-⊤ : ⇓W⇑ ⊤ {0}
⇓W⇑-⊤ = ⇓W⇑[ const ε , const tt ]
\end{code}
%</Synth-Unit>


%<*Synth-Product>
\begin{code}
⇓W⇑-× : ∀ {α i β j} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ (α × β)
⇓W⇑-× {α} {i} {β} {j} sα sβ = ⇓W⇑[ down , up ]
    where down : (α × β) → W (i + j)
          down (a , b) = (⇓ a) ++ (⇓ b)

          up : W (i + j) → (α × β)
          up w with splitAt i w
          up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = ⇑ ⇓a , ⇑ ⇓b
\end{code}
%</Synth-Product>


%<*Synth-Vec>
\begin{code}
⇓W⇑-Vec : ∀ {α i n} → ⇓W⇑ α {i} → ⇓W⇑ (Vec α n)
⇓W⇑-Vec {α} {i} {n} sα = ⇓W⇑[ down , up ]
    where down : Vec α n → W (n * i)
          down v = v >>= ⇓

          up : W (n * i) → Vec α n
          up w = mapᵥ ⇑ (proj₁ $ group n i w)
\end{code}
%</Synth-Vec>


-- Sum-related tagging helpers
%<*untag>
\begin{code}
untag : ∀ {i j} → W (suc (i ⊔ j)) → W i ⊎ W j
untag {i} {j} (t ◁ ab) with toℕ (atom→n t) ≟ 1
untag {i} {j} (t ◁ ab) | yes _ = inj₂ (unpadSnd i j ab)
untag {i} {j} (t ◁ ab) | no  _ = inj₁ (unpadFst i j ab)
\end{code}
%</untag>

%<*untagList>
\begin{code}
untagList : ∀ {i j} → List (W (suc (i ⊔ j))) → List (W i) × List (W j)
untagList = segregateSums ∘ mapₗ untag
\end{code}
%</untagList>


-- TODO: guarantee that n₁ and n₂ are different?
%<*Synth-Sum>
\begin{code}
⇓W⇑-⊎ : ∀ {α i β j} → (n m p : Atom#) {d : n ≢ m} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ (α ⊎ β) {suc (i ⊔ j)}
⇓W⇑-⊎ {α} {i} {β} {j} n m p sα sβ = ⇓W⇑[ down , up ]
    where down : α ⊎ β → W (suc (i ⊔ j))
          down = [ (λ a → (n→atom n) ◁ padFst i j (n→atom p) (⇓ a))
                 , (λ b → (n→atom m) ◁ padSnd i j (n→atom p) (⇓ b)) ]
          
          up : W (suc (i ⊔ j)) → α ⊎ β
          up = map⊎ ⇑ ⇑ ∘ untag
\end{code}
%</Synth-Sum>


-- derivable instances (can be resolved recursively from the basic)
\begin{code}
⇓W⇑-[a×b]×c : ∀ {α i β j γ k} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ ((α × β) × γ)
⇓W⇑-a×[b×c] : ∀ {α i β j γ k} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ (α × (β × γ))
\end{code}

\begin{code}
⇓W⇑-a×[b×c] sα sβ sγ = ⇓W⇑-× sα            (⇓W⇑-× sβ sγ)
⇓W⇑-[a×b]×c sα sβ sγ = ⇓W⇑-× (⇓W⇑-× sα sβ) sγ
\end{code}


\begin{code}
⇓W⇑-a×[b×[c×d]] : ∀ {α i β j γ k δ l} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ δ {l} → ⇓W⇑ (α × (β × (γ × δ)))
⇓W⇑-a×[[b×c]×d] : ∀ {α i β j γ k δ l} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ δ {l} → ⇓W⇑ (α × ((β × γ) × δ))
⇓W⇑-[a×b]×[c×d] : ∀ {α i β j γ k δ l} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ δ {l} → ⇓W⇑ ((α × β) × (γ × δ))
⇓W⇑-[a×[b×c]]×d : ∀ {α i β j γ k δ l} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ δ {l} → ⇓W⇑ ((α × (β × γ)) × δ)
⇓W⇑-[[a×b]×c]×d : ∀ {α i β j γ k δ l} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ γ {k} → ⇓W⇑ δ {l} → ⇓W⇑ (((α × β) × γ) × δ)
\end{code}

\begin{code}
⇓W⇑-a×[b×[c×d]] sα sβ sγ sδ = ⇓W⇑-× sα                     (⇓W⇑-a×[b×c] sβ sγ sδ)
⇓W⇑-a×[[b×c]×d] sα sβ sγ sδ = ⇓W⇑-× sα                     (⇓W⇑-[a×b]×c sβ sγ sδ)
⇓W⇑-[a×[b×c]]×d sα sβ sγ sδ = ⇓W⇑-× (⇓W⇑-a×[b×c] sα sβ sγ) sδ
⇓W⇑-[[a×b]×c]×d sα sβ sγ sδ = ⇓W⇑-× (⇓W⇑-[a×b]×c sα sβ sγ) sδ
⇓W⇑-[a×b]×[c×d] sα sβ sγ sδ = ⇓W⇑-× (⇓W⇑-× sα sβ) (⇓W⇑-× sγ sδ)
\end{code}


\begin{code}
⇓W⇑-a×[Vec[b]] : ∀ {α i β j} → {n : ℕ} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ (α × Vec β n)
⇓W⇑-Vec[a]×b   : ∀ {α i β j} → {n : ℕ} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ (Vec α n × β)
⇓W⇑-Vec[a×b]   : ∀ {α i β j} → {n : ℕ} → ⇓W⇑ α {i} → ⇓W⇑ β {j} → ⇓W⇑ (Vec (α × β) n)
\end{code}

\begin{code}
⇓W⇑-a×[Vec[b]] {n = m} sα sβ = ⇓W⇑-× sα           (⇓W⇑-Vec sβ)
⇓W⇑-Vec[a]×b   {n = m} sα sβ = ⇓W⇑-× (⇓W⇑-Vec sα) sβ
⇓W⇑-Vec[a×b]   {n = m} sα sβ = ⇓W⇑-Vec {n = m} (⇓W⇑-× sα sβ)
\end{code}
