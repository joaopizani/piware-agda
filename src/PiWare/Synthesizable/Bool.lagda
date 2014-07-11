\begin{code}
module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Nat using (suc; _⊔_)
open import Data.Bool using () renaming (Bool to B)
open import Data.Vec using (Vec; head) renaming ([_] to singleton)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B

import PiWare.Atom as A
open A.Atomic Atomic-B using (Atom#)
\end{code}


-- basic instance
%<*Synth-Bool>
\begin{code}
⇓W⇑-B : ⇓W⇑ B
⇓W⇑-B = ⇓W⇑[ singleton , head ]
\end{code}
%</Synth-Bool>


-- derivable instances (can be resolved recursively from the basics)
%<*Synth-Bool-Product-types>
\begin{code}
⇓W⇑-B×α : ∀ {α i} → ⇓W⇑ α {i} → ⇓W⇑ (B × α)
⇓W⇑-α×B : ∀ {α i} → ⇓W⇑ α {i} → ⇓W⇑ (α × B)
\end{code}
%</Synth-Bool-Product-types>

%<*Synth-Bool-Product-defs>
\begin{code}
⇓W⇑-B×α sα = ⇓W⇑-× ⇓W⇑-B sα
⇓W⇑-α×B sα = ⇓W⇑-× sα     ⇓W⇑-B
\end{code}
%</Synth-Bool-Product-defs>


%<*Synth-Bool-Vec>
\begin{code}
⇓W⇑-VecB : ∀ {n} → ⇓W⇑ (Vec B n)
⇓W⇑-VecB = ⇓W⇑-Vec ⇓W⇑-B
\end{code}
%</Synth-Bool-Vec>


%<*Synth-Bool-Sum-types>
\begin{code}
⇓W⇑-B⊎α : ∀ {α i} → (n₁ n₂ p : Atom#) {diff : n₁ ≢ n₂} → ⇓W⇑ α {i} → ⇓W⇑ (B ⊎ α) {suc (1 ⊔ i)}
⇓W⇑-α⊎B : ∀ {α i} → (n₁ n₂ p : Atom#) {diff : n₁ ≢ n₂} → ⇓W⇑ α {i} → ⇓W⇑ (α ⊎ B) {suc (i ⊔ 1)}
\end{code}
%</Synth-Bool-Sum-types>

%<*Synth-Bool-Sum-defs>
\begin{code}
⇓W⇑-B⊎α n₁ n₂ p sα = ⇓W⇑-⊎ n₁ n₂ p ⇓W⇑-B sα
⇓W⇑-α⊎B n₁ n₂ p sα = ⇓W⇑-⊎ n₁ n₂ p sα     ⇓W⇑-B
\end{code}
%</Synth-Bool-Sum-defs>


\begin{code}
⇓W⇑-B×B : ⇓W⇑ (B × B)
⇓W⇑-B×B = ⇓W⇑-× ⇓W⇑-B ⇓W⇑-B
\end{code}

\begin{code}
⇓W⇑-[B×B]×B : ⇓W⇑ ((B × B) × B)
⇓W⇑-B×[B×B] : ⇓W⇑ (B × (B × B))
\end{code}

\begin{code}
⇓W⇑-[B×B]×B = ⇓W⇑-[a×b]×c ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
⇓W⇑-B×[B×B] = ⇓W⇑-a×[b×c] ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
\end{code}

\begin{code}
⇓W⇑-B×[B×[B×B]] : ⇓W⇑ (B × (B × (B × B)))
⇓W⇑-B×[[B×B]×B] : ⇓W⇑ (B × ((B × B) × B))
⇓W⇑-[B×B]×[B×B] : ⇓W⇑ ((B × B) × (B × B))
⇓W⇑-[B×[B×B]]×B : ⇓W⇑ ((B × (B × B)) × B)
⇓W⇑-[[B×B]×B]×B : ⇓W⇑ (((B × B) × B) × B)
\end{code}

\begin{code}
⇓W⇑-B×[B×[B×B]] = ⇓W⇑-a×[b×[c×d]] ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
⇓W⇑-B×[[B×B]×B] = ⇓W⇑-a×[[b×c]×d] ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
⇓W⇑-[B×B]×[B×B] = ⇓W⇑-[a×b]×[c×d] ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
⇓W⇑-[B×[B×B]]×B = ⇓W⇑-[a×[b×c]]×d ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
⇓W⇑-[[B×B]×B]×B = ⇓W⇑-[[a×b]×c]×d ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B ⇓W⇑-B
\end{code}
