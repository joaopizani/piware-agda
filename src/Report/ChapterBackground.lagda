\begin{code}
module Report.ChapterBackground where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
\end{code}


%<*tail-decl>
\begin{code}
tail : {α : Set} {n : ℕ} → Vec α (suc n) → Vec α n
\end{code}
%</tail-decl>
%<*tail-def>
\begin{code}
tail (x ∷ xs) = xs
\end{code}
%</tail-def>

%<*Pair>
\begin{code}
record Σ (α : Set) (β : α → Set) : Set where
    constructor _,_
    field
        fst : α
        snd : β fst
\end{code}
%</Pair>

%<*take-decl>
\begin{code}
take : {α : Set} {n : ℕ} (k : ℕ) → Vec α (k + n) → Vec α k
\end{code}
%</take-decl>
%<*take-def>
\begin{code}
take zero    _        = []
take (suc k) (x ∷ xs) = x ∷ take k xs
\end{code}
%</take-def>

%<*nat-le>
\begin{code}
data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ}   → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
%</nat-le>

%<*le-two-four>
\begin{code}
twoLEQFour : 2 ≤ 4
twoLEQFour = s≤s (s≤s z≤n)
\end{code}
%</le-two-four>

%<*le-trans>
\begin{code}
≤trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤trans z≤n       _         = z≤n
≤trans (s≤s ab') (s≤s bc') = s≤s (≤trans ab' bc')
\end{code}
%</le-trans>

%<*take-proof-decl>
\begin{code}
take' : {α : Set} {n : ℕ} (m : ℕ) {p : m ≤ n} → Vec α n → Vec α m
\end{code}
%</take-proof-decl>
%<*take-proof-def>
\begin{code}
take' zero    _                  = []
take' (suc m) {()}      []
take' (suc m) {s≤s m≤n} (x ∷ xs) = x ∷ take' m {m≤n} xs
\end{code}
%</take-proof-def>
