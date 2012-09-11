-- NONDETERMINISTIC COMPUTATIONS
-- Failure
class Monad m => MonadFail m where
  fail' :: m a

skip :: Monad m => m ()
skip = return ()

guard :: MonadFail m => Bool -> m ()
guard True  = skip
guard False = fail'

assert :: MonadFail m => (a -> Bool) -> m a -> m a
assert p mx = do {x <- mx; guard (p x); return x}

-- Choice
class Monad m => MonadAlt m where
  op :: m a -> m a -> m a
  
-- Nondeterminism
class (MonadFail m, MonadAlt m) => MonadNondet m where
    
{-
instance Monad [] where
  return x = [x]
  xs >>= f = concat (map f xs)
-}

instance MonadFail [] where
  fail' = []
  
instance MonadAlt [] where
  op = (++)
  
-- Permutations
select :: MonadNondet m => [a] -> m(a,[a])
select []     = fail'
select (x:xs) = op (return (x,xs)) (do {(y,ys) <- select xs; return (y,x:ys)}) 

perms :: MonadNondet m => [a] -> m [a]
perms [] = return []
perms xs = do {(y,ys) <- select xs; zs <- perms ys; return (y:zs)}