\begin{code}
module Category.Functor.Extra where

open import Function using (id)
open import Category.Functor using (RawFunctor)
\end{code}


-- the identity functor
%<*IdF>
\AgdaTarget{IdF}
\begin{code}
IdF : ∀ {ℓ} → RawFunctor {ℓ} id
IdF = record { _<$>_ = id }
\end{code}
%</IdF>
