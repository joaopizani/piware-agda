\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Plugs.Typed {At : Atomic} (Gt : Gates At) where

open import Data.Unit using (⊤)
open import Data.Nat using (suc; _+_; _*_)
open import Data.Vec using (Vec)
open import Data.Product using (_×_)

open import Algebra using (module CommutativeSemiring)
open import Data.Nat.Properties using () renaming (commutativeSemiring to ℕ-commSemiring)
open import Algebra.Operations (CommutativeSemiring.semiring ℕ-commSemiring) using (_^_)

open import PiWare.Synthesizable At using (⇓W⇑; ⇓W⇑-×; ⇓W⇑-Vec)
open import PiWare.Circuit.Typed Gt using (𝐂̂; Mkℂ̂)
open import PiWare.Plugs Gt
    using ( nil⤨; id⤨; swap⤨; intertwine⤨; ALR⤨; ARL⤨; head⤨; vecHalf⤨; vecHalfPow⤨
          ; fst⤨; snd⤨; singleton⤨; forkVec⤨; fork×⤨; uncons⤨; cons⤨)
\end{code}


%<*nil-plug-typed>
\AgdaTarget{nil⤨̂}
\begin{code}
nil⤨̂ : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ α ⊤
nil⤨̂ ⦃ sα ⦄ = Mkℂ̂ ⦃ sα ⦄ nil⤨
\end{code}
%</nil-plug-typed>


%<*id-plug-typed>
\AgdaTarget{id⤨̂}
\begin{code}
id⤨̂ : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ α α
id⤨̂ ⦃ sα ⦄ = Mkℂ̂ ⦃ sα ⦄ ⦃ sα ⦄ id⤨
\end{code}
%</id-plug-typed>


%<*swap-plug-typed>
\AgdaTarget{swap⤨̂}
\begin{code}
swap⤨̂ : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → 𝐂̂ (α × β) (β × α)
swap⤨̂ {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sα ⦄ ⦄ (swap⤨ {i} {j})
\end{code}
%</swap-plug-typed>


%<*intertwine-plug-typed>
\AgdaTarget{intertwine⤨̂}
\begin{code}
intertwine⤨̂ : ∀ {α i β j γ k δ l} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ ⦃ _ : ⇓W⇑ δ {l} ⦄
              → 𝐂̂ ((α × β) × (γ × δ)) ((α × γ) × (β × δ))
intertwine⤨̂ {i = i} {j = j} {k = k} {l = l} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ ⦃ sδ ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sγ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sδ ⦄ ⦄ ⦄
        (intertwine⤨ {i} {j} {k} {l})
\end{code}
%</intertwine-plug-typed>


-- associativity plugs
%<*ALR-plug-typed>
\AgdaTarget{ALR⤨̂}
\begin{code}
ALR⤨̂ : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ → 𝐂̂ ((α × β) × γ) (α × (β × γ))
ALR⤨̂ {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄ (ALR⤨ {i} {j} {k})
\end{code}
%</ALR-plug-typed>


%<*ARL-plug-typed>
\AgdaTarget{ARL⤨̂}
\begin{code}
ARL⤨̂ : ∀ {α i β j γ k} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ ⦃ _ : ⇓W⇑ γ {k} ⦄ → 𝐂̂ (α × (β × γ)) ((α × β) × γ)
ARL⤨̂ {i = i} {j = j} {k = k} ⦃ sα ⦄ ⦃ sβ ⦄ ⦃ sγ ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sβ ⦄ ⦃ sγ ⦄ ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sγ ⦄ ⦄ (ARL⤨ {i} {j} {k})
\end{code}
%</ARL-plug-typed>
 

-- vector plugs
%<*head-plug-typed>
\AgdaTarget{head⤨̂}
\begin{code}
head⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ (Vec α (suc n)) α
head⤨̂ {_} {i} {m} ⦃ sα ⦄ = Mkℂ̂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ sα ⦄ (head⤨ {m} {i})
\end{code}
%</head-plug-typed>


%<*uncons-plug-typed>
\AgdaTarget{uncons⤨̂}
\begin{code}
uncons⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ (Vec α (suc n)) (α × Vec α n)
uncons⤨̂ {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ (uncons⤨ {i} {m})
\end{code}
%</uncons-plug-typed>


%<*cons-plug-typed>
\AgdaTarget{cons⤨̂}
\begin{code}
cons⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ (α × Vec α n) (Vec α (suc n))
cons⤨̂ {_} {i} {m} ⦃ sα ⦄ = Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ (cons⤨ {i} {m})
\end{code}
%</cons-plug-typed>


%<*singleton-plug-typed>
\AgdaTarget{singleton⤨̂}
\begin{code}
singleton⤨̂ : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ α (Vec α 1)
singleton⤨̂ {_} {i} ⦃ sα ⦄ = Mkℂ̂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = 1} ⦃ sα ⦄ ⦄ (singleton⤨ {i}) 
\end{code}
%</singleton-plug-typed>


%<*vecHalf-plug-typed>
\AgdaTarget{vecHalf⤨̂}
\begin{code}
vecHalf⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ (Vec α (2 * suc n)) (Vec α (suc n) × Vec α (suc n))
vecHalf⤨̂ {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-Vec {n = 2 * suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = suc m} ⦃ sα ⦄ ⦄ ⦄
        (vecHalf⤨ {m} {i})
\end{code}
%</vecHalf-plug-typed>


%<*vecHalfPow-plug-typed>
\AgdaTarget{vecHalfPow⤨̂}
\begin{code}
vecHalfPow⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ (Vec α (2 ^ suc n)) (Vec α (2 ^ n) × Vec α (2 ^ n))
vecHalfPow⤨̂ {_} {i} {m} ⦃ sα ⦄ =
    Mkℂ̂ ⦃ ⇓W⇑-Vec {n = 2 ^ suc m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-× ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦃ ⇓W⇑-Vec {n = 2 ^ m} ⦃ sα ⦄ ⦄ ⦄ 
        (vecHalfPow⤨ {m} {i})
\end{code}
%</vecHalfPow-plug-typed>


%<*forkVec-plug-typed>
\AgdaTarget{forkVec⤨̂}
\begin{code}
forkVec⤨̂ : ∀ {α i n} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ α (Vec α n)
forkVec⤨̂ {_} {i} {m} ⦃ sα ⦄ = Mkℂ̂ ⦃ sα ⦄ ⦃ ⇓W⇑-Vec {n = m} ⦃ sα ⦄ ⦄ (forkVec⤨ {m} {i})
\end{code}
%</forkVec-plug-typed>


%<*forkProduct-plug-typed>
\AgdaTarget{fork×⤨̂}
\begin{code}
fork×⤨̂ : ∀ {α i} ⦃ _ : ⇓W⇑ α {i} ⦄ → 𝐂̂ α (α × α)
fork×⤨̂ {_} {i} ⦃ sα ⦄ = Mkℂ̂ ⦃ sα ⦄ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sα ⦄ ⦄ (fork×⤨ {i})
\end{code}
%</forkProduct-plug-typed>


-- pairs
%<*fst-plug-typed>
\AgdaTarget{fst⤨̂}
\begin{code}
fst⤨̂ : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → 𝐂̂ (α × β) α
fst⤨̂ {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sα ⦄ (fst⤨ {i} {j})
\end{code}
%</fst-plug-typed>


%<*snd-plug-typed>
\AgdaTarget{snd⤨̂}
\begin{code}
snd⤨̂ : ∀ {α i β j} ⦃ _ : ⇓W⇑ α {i} ⦄ ⦃ _ : ⇓W⇑ β {j} ⦄ → 𝐂̂ (α × β) β
snd⤨̂ {i = i} {j = j} ⦃ sα ⦄ ⦃ sβ ⦄ = Mkℂ̂ ⦃ ⇓W⇑-× ⦃ sα ⦄ ⦃ sβ ⦄ ⦄ ⦃ sβ ⦄ (snd⤨ {i} {j})
\end{code}
%</snd-plug-typed>
