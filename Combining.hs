{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

import NonDet
import MyMonad
import Stateful
import Control.Monad.State hiding (guard, return)
import Prelude hiding (Monad, return, fail)

class (MonadState s m, MonadNondet m) => 
      MonadStateNondet s m | m -> s
{- Se debe cumplir
  m >> fail = fail
  m >>= \x -> k1 x `op` k2 x = (m >>= k1) `op` (m >>= k2)
-}
                             
queens1 n = do
  s <- get
  rs <- perms [1..n]
  put empty
  ok <- safe2 (place n rs)
  put s
  guard ok
  return rs
  
{-queens2 n = do
  s <- get
  rs <- perms [1..n]
  put empty
  ok <- safe2 (place n rs)
  guard ok
  put s
  return rs-}
 {- 
safe3 crs = foldr step3 skip
step3 cr m = m >> 
             do {uds <- get;let (b, uds') = test cr uds;put uds';guard b}

queens3 n = do
  s <- get
  rs <- perms [1..n]
  put empty
  safe3 (place n rs)
  put s
  return rs-}