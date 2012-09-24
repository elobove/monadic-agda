module MyMonad where

import Prelude hiding (Monad, return, fail)

-- MONAD CLASS
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- CLASSES OF MONAD
class Monad m => MonadCount m where
  tick :: m ()
  tick = return ()

-- Failure
class Monad m => MonadFail m where
  fail :: m a

-- Choice
class Monad m => MonadAlt m where
  sq :: m a -> m a -> m a

-- Nondeterminism
class (MonadFail m, MonadAlt m) => MonadNondet m where

-- Exception
class MonadFail m => MonadExcept m where
  catch :: m a -> m a -> m a

-- INSTANCES
instance Monad [] where
  return x = [x]
  xs >>= f = concat(map f xs)

instance Monad Maybe where
  return x = Just x
  Just x >>= f = f x
  Nothing >>= _ = Nothing

instance MonadFail [] where
  fail = []

instance MonadAlt [] where
  sq = (++)

instance MonadNondet [] where

{-instance MonadExcept [] where
  catch m h = if m == fail then h else m-}

-- EXTRA FUNCTIONS
skip :: Monad m => m ()
skip = return ()