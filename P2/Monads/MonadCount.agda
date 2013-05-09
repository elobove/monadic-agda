module Monads.MonadCount where

open import Abel.Category.Monad
open import Data.Unit

------------------------------------------------------------------
-- MonadCount

record MonadCount {M : Set → Set} (monad : Monad M) : Set₁ where
  constructor mkMonadCount

  open Monad monad

  field
    tick : M ⊤