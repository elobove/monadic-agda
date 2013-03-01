module Monads.MonadCount where

open import Abel.Category.Monad
open import Abel.Category.Applicative
open import Abel.Category.Functor

open import Data.Maybe
open import Data.Nat
open import Monads.Data.Tuple

------------------------------------------------------------------
-- MonadCount

record MonadCount (M : Set → Set) {monad : Monad M} : Set₁ where
  constructor
    mkMonadCount

  open Monad monad

  field
    tick : ∀{A} → M A

---- ADVERTENCIA: no estan bien definidas, en vez de M A debería ser M ()

monadCount : MonadCount Maybe {monad}
monadCount = mkMonadCount tick
  where
    open Monad monad

    tick : {A : Set} -> Maybe A
    tick = nothing

-- skip : {A : Set} {M : Monad} → M A
-- skip = return nothing

-- hanoi : {A : Set} {M : MonadCount} → ℕ → M A
-- hanoi zero    = tick
-- hanoi (suc n) = hanoi n >> tick >> hanoi n

-- rep : {A : Set} {M : Set → Set} {monad : Monad M} → ℕ → M A → M A
-- rep zero    mx = skip
-- rep (suc n) mx = mx >> rep n mx