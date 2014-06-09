\begin{code}
module PiWare.Synthesizable.Bool where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Vec using (Vec; head) renaming ([_] to singleton)

open import PiWare.Atom.Bool using (Atom𝔹)
open import PiWare.Synthesizable Atom𝔹 public

import PiWare.Atom as A
open A.AtomInfo Atom𝔹 using (Atom#)
\end{code}


-- basic instance
\begin{code}
⇓𝕎⇑-𝔹 : ⇓𝕎⇑ 𝔹
⇓𝕎⇑-𝔹 = ⇓𝕎⇑[ singleton , head ]
\end{code}


-- derivable instances (can be resolved recursively from the basics)
\begin{code}
⇓𝕎⇑-𝔹×α : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (𝔹 × α)
⇓𝕎⇑-α×𝔹 : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (α × 𝔹)
\end{code}

\begin{code}
⇓𝕎⇑-𝔹×α sα = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 sα
⇓𝕎⇑-α×𝔹 sα = ⇓𝕎⇑-× sα     ⇓𝕎⇑-𝔹
\end{code}


\begin{code}
⇓𝕎⇑-Vec𝔹 : ∀ {n} → ⇓𝕎⇑ (Vec 𝔹 n)
⇓𝕎⇑-Vec𝔹 = ⇓𝕎⇑-Vec ⇓𝕎⇑-𝔹
\end{code}


\begin{code}
⇓𝕎⇑-𝔹⊎α' : ∀ {α i} → (n₁ n₂ p : Atom#) → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (𝔹 ⊎ α) {suc (1 ⊔ i)}
⇓𝕎⇑-α⊎𝔹' : ∀ {α i} → (n₁ n₂ p : Atom#) → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (α ⊎ 𝔹) {suc (i ⊔ 1)}
\end{code}

\begin{code}
⇓𝕎⇑-𝔹⊎α : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (𝔹 ⊎ α) {suc (1 ⊔ i)}
⇓𝕎⇑-α⊎𝔹 : ∀ {α i} → ⇓𝕎⇑ α {i} → ⇓𝕎⇑ (α ⊎ 𝔹) {suc (i ⊔ 1)}
\end{code}

\begin{code}
⇓𝕎⇑-𝔹⊎α' n₁ n₂ p sα = ⇓𝕎⇑-⊎' n₁ n₂ p ⇓𝕎⇑-𝔹 sα
⇓𝕎⇑-α⊎𝔹' n₁ n₂ p sα = ⇓𝕎⇑-⊎' n₁ n₂ p sα     ⇓𝕎⇑-𝔹
\end{code}

\begin{code}
⇓𝕎⇑-𝔹⊎α sα = ⇓𝕎⇑-⊎ ⇓𝕎⇑-𝔹 sα
⇓𝕎⇑-α⊎𝔹 sα = ⇓𝕎⇑-⊎ sα     ⇓𝕎⇑-𝔹
\end{code}



\begin{code}
⇓𝕎⇑-𝔹×𝔹 : ⇓𝕎⇑ (𝔹 × 𝔹)
⇓𝕎⇑-𝔹×𝔹 = ⇓𝕎⇑-× ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
\end{code}

\begin{code}
⇓𝕎⇑-[𝔹×𝔹]×𝔹 : ⇓𝕎⇑ ((𝔹 × 𝔹) × 𝔹)
⇓𝕎⇑-𝔹×[𝔹×𝔹] : ⇓𝕎⇑ (𝔹 × (𝔹 × 𝔹))
\end{code}

\begin{code}
⇓𝕎⇑-[𝔹×𝔹]×𝔹 = ⇓𝕎⇑-[a×b]×c ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-𝔹×[𝔹×𝔹] = ⇓𝕎⇑-a×[b×c] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
\end{code}

\begin{code}
⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] : ⇓𝕎⇑ (𝔹 × (𝔹 × (𝔹 × 𝔹)))
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] : ⇓𝕎⇑ (𝔹 × ((𝔹 × 𝔹) × 𝔹))
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] : ⇓𝕎⇑ ((𝔹 × 𝔹) × (𝔹 × 𝔹))
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 : ⇓𝕎⇑ ((𝔹 × (𝔹 × 𝔹)) × 𝔹)
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 : ⇓𝕎⇑ (((𝔹 × 𝔹) × 𝔹) × 𝔹)
\end{code}

\begin{code}
⇓𝕎⇑-𝔹×[𝔹×[𝔹×𝔹]] = ⇓𝕎⇑-a×[b×[c×d]] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-𝔹×[[𝔹×𝔹]×𝔹] = ⇓𝕎⇑-a×[[b×c]×d] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[𝔹×𝔹]×[𝔹×𝔹] = ⇓𝕎⇑-[a×b]×[c×d] ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[𝔹×[𝔹×𝔹]]×𝔹 = ⇓𝕎⇑-[a×[b×c]]×d ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
⇓𝕎⇑-[[𝔹×𝔹]×𝔹]×𝔹 = ⇓𝕎⇑-[[a×b]×c]×d ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹 ⇓𝕎⇑-𝔹
\end{code}
