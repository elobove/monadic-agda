-- | TOWERS OF HANOI
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

class Monad m => MonadCount m where
  tick :: m ()
  -- tick = return ()
                  
instance MonadCount IO where
  tick = return ()
  
-- deriving instance Eq (IO ())

instance Monad m => Eq (m ()) where
  m1 == m2 = () == ()
  
hanoi :: MonadCount m => Int -> m () 
hanoi 0 = skip
hanoi n = hanoi (n-1) >> tick >> hanoi (n-1)

skip :: Monad m => m ()
skip = return ()

rep :: Monad m => Int -> m () -> m ()
rep 0 mx = skip
rep n mx = mx >> rep (n-1) mx
