------------------------------------------------------------------------------
-- | MonadState: Supports stateful computations
------------------------------------------------------------------------------

module Proof.MonadState where

open import Abel.Category.Monad
open import Data.Unit

------------------------------------------------------------------
-- MonadState

record MonadState {M : Set → Set} (S : Set) (monad : Monad'' M) : Set₁ where

  constructor
    mkMonadState

  open Monad'' monad

  field
    get : M S

    put : S → M ⊤
