------------------------------------------------------------------------------
-- | MonadState: Supports stateful computations
------------------------------------------------------------------------------

module Proof.MonadState where

open import Proof.Monad
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------
-- MonadState

record MonadState {M : Set → Set} (S : Set) (monad : Monad M) : Set₁ where

  constructor
    mkMonadState

  open Monad monad

  field
    get : M S

    put : S → M ⊤

    put-put : {s₁ s₂ : S} → (put s₁ >> put s₂) ≡ put s₂

    put-get : {s : S} → (put s >> get) ≡ (put s >> return s)

    get-put : (get >>= put) ≡ skip

    --get-get : {A : Set} {k : S → M S} → (get >>= (λ s → (get >>= k s))) ≡ (get >>= (λ s → k s s))
