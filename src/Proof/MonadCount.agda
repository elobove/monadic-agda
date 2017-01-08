------------------------------------------------------------------------------
-- | MonadCount: Supports effect of counting
------------------------------------------------------------------------------

module Proof.MonadCount where

open import Proof.Monad
open import Data.Unit

------------------------------------------------------------------
-- MonadCount

record MonadCount {M : Set → Set} (monad : Monad M) : Set₁ where
  constructor mkMonadCount

  field
    tick : M ⊤
