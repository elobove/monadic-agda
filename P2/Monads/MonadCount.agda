module Monads.MonadCount where

open import Abel.Category.Monad
open import Abel.Category.Applicative
open import Abel.Category.Functor

record MonadCount {M : Set → Set} {monad : Monad M} : Set1 where
  constructor 
    mkMonadCount

  field
    tick : ∀ {A} → M A

---- ADVERTENCIA: no estan bien definidas, en vez de M A debería ser M ()

-- monadCount : MonadCount Maybe
-- monadCount = mkMonadCount tick
--  where
--    tick : {A : Set} -> Maybe A
--    tick = nothing

-- skip {A : Set} {M : Set → Set} {monad : Monad M} → M A
-- skip = return

-- hanoi : {A : Set} {M : Set → Set} {monad : Monad M} → Nat → M A
-- hanoi zero    = skip
-- hanoi (suc n) = hanoi n >> tick >> hanoi n

-- rep : {A : Set} {M : Set → Set} {monad : Monad M} → Nat → M A → M A
-- rep zero    mx = skip
-- rep (suc n) mx = mx >> rep n mx