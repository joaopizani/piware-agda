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
𝕎 : ℕ → Set
𝕎 = Vec Atom
\end{code}
%</Word>


-- Provides a mapping between "high-level" metalanguage types and words
-- TODO: proofs that ⇑ and ⇓ are inverses
%<*Synth>
\begin{code}
record ⇓𝕎⇑ (α : Set) {i : ℕ} : Set where
    constructor ⇓𝕎⇑[_,_]
    field
        ⇓ : α → 𝕎 i
        ⇑ : 𝕎 i → α
\end{code}
%</Synth>

\begin{code}
open ⇓𝕎⇑ ⦃ ... ⦄
\end{code}


-- basic instances
%<*Synth-Unit>
\begin{code}
⇓𝕎⇑-⊤ : ⇓𝕎⇑ ⊤ {0}
⇓𝕎⇑-⊤ = ⇓𝕎⇑[ const ε , const tt ]
\end{code}
%</Synth-Unit>


%<*Synth-Product>
\begin{code}
⇓𝕎⇑-× : ∀ {α i β j} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α × β)
⇓𝕎⇑-× {α} {i} {β} {j} sα sβ = ⇓𝕎⇑[ down , up ]
    where down : (α × β) → 𝕎 (i + j)
          down (a , b) = (⇓ a) ++ (⇓ b)

          up : 𝕎 (i + j) → (α × β)
          up w with splitAt i w
          up .(⇓a ++ ⇓b) | ⇓a , ⇓b , refl = ⇑ ⇓a , ⇑ ⇓b
\end{code}
%</Synth-Product>


%<*Synth-Vec>
\begin{code}
⇓𝕎⇑-Vec : ∀ {α i n} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (Vec α n)
⇓𝕎⇑-Vec {α} {i} {n} sα = ⇓𝕎⇑[ down , up ]
    where down : Vec α n → 𝕎 (n * i)
          down v = v >>= ⇓

          up : 𝕎 (n * i) → Vec α n
          up w = mapᵥ ⇑ (proj₁ $ group n i w)
\end{code}
%</Synth-Vec>


-- Sum-related tagging helpers
%<*untag>
\begin{code}
untag : ∀ {i j} → 𝕎 (suc (i ⊔ j)) → 𝕎 i ⊎ 𝕎 j
untag {i} {j} (t ◁ ab) with toℕ (atom→n t) ≟ 1
untag {i} {j} (t ◁ ab) | yes _ = inj₂ (unpadSnd i j ab)
untag {i} {j} (t ◁ ab) | no  _ = inj₁ (unpadFst i j ab)
\end{code}
%</untag>

%<*untagList>
\begin{code}
untagList : ∀ {i j} → List (𝕎 (suc (i ⊔ j))) → List (𝕎 i) × List (𝕎 j)
untagList = segregateSums ∘ mapₗ untag
\end{code}
%</untagList>


-- TODO: guarantee that n₁ and n₂ are different?
%<*Synth-Sum>
\begin{code}
⇓𝕎⇑-⊎ : ∀ {α i β j} → (n m p : Atom#) {d : n ≢ m} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α ⊎ β) {suc (i ⊔ j)}
⇓𝕎⇑-⊎ {α} {i} {β} {j} n m p sα sβ = ⇓𝕎⇑[ down , up ]
    where down : α ⊎ β → 𝕎 (suc (i ⊔ j))
          down = [ (λ a → (n→atom n) ◁ padFst i j (n→atom p) (⇓ a))
                 , (λ b → (n→atom m) ◁ padSnd i j (n→atom p) (⇓ b)) ]
          
          up : 𝕎 (suc (i ⊔ j)) → α ⊎ β
          up = map⊎ ⇑ ⇑ ∘ untag
\end{code}
%</Synth-Sum>


-- derivable instances (can be resolved recursively from the basic)
\begin{code}
⇓𝕎⇑-[a×b]×c : ∀ {α i β j γ k} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ ((α × β) × γ)
⇓𝕎⇑-a×[b×c] : ∀ {α i β j γ k} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ (α × (β × γ))
\end{code}

\begin{code}
⇓𝕎⇑-a×[b×c] sα sβ sγ = ⇓𝕎⇑-× sα            (⇓𝕎⇑-× sβ sγ)
⇓𝕎⇑-[a×b]×c sα sβ sγ = ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) sγ
\end{code}


\begin{code}
⇓𝕎⇑-a×[b×[c×d]] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (α × (β × (γ × δ)))
⇓𝕎⇑-a×[[b×c]×d] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (α × ((β × γ) × δ))
⇓𝕎⇑-[a×b]×[c×d] : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ ((α × β) × (γ × δ))
⇓𝕎⇑-[a×[b×c]]×d : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ ((α × (β × γ)) × δ)
⇓𝕎⇑-[[a×b]×c]×d : ∀ {α i β j γ k δ l} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ γ {k} → ⇓𝕎⇑ δ {l} → ⇓𝕎⇑ (((α × β) × γ) × δ)
\end{code}

\begin{code}
⇓𝕎⇑-a×[b×[c×d]] sα sβ sγ sδ = ⇓𝕎⇑-× sα                     (⇓𝕎⇑-a×[b×c] sβ sγ sδ)
⇓𝕎⇑-a×[[b×c]×d] sα sβ sγ sδ = ⇓𝕎⇑-× sα                     (⇓𝕎⇑-[a×b]×c sβ sγ sδ)
⇓𝕎⇑-[a×[b×c]]×d sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-a×[b×c] sα sβ sγ) sδ
⇓𝕎⇑-[[a×b]×c]×d sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-[a×b]×c sα sβ sγ) sδ
⇓𝕎⇑-[a×b]×[c×d] sα sβ sγ sδ = ⇓𝕎⇑-× (⇓𝕎⇑-× sα sβ) (⇓𝕎⇑-× sγ sδ)
\end{code}


\begin{code}
⇓𝕎⇑-a×[Vec[b]] : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (α × Vec β n)
⇓𝕎⇑-Vec[a]×b   : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (Vec α n × β)
⇓𝕎⇑-Vec[a×b]   : ∀ {α i β j} → {n : ℕ} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ β {j} → ⇓𝕎⇑ (Vec (α × β) n)
\end{code}

\begin{code}
⇓𝕎⇑-a×[Vec[b]] {n = m} sα sβ = ⇓𝕎⇑-× sα           (⇓𝕎⇑-Vec sβ)
⇓𝕎⇑-Vec[a]×b   {n = m} sα sβ = ⇓𝕎⇑-× (⇓𝕎⇑-Vec sα) sβ
⇓𝕎⇑-Vec[a×b]   {n = m} sα sβ = ⇓𝕎⇑-Vec {n = m} (⇓𝕎⇑-× sα sβ)
\end{code}
