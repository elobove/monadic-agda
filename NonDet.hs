module NonDet where

import Prelude hiding (Monad, return, fail)
import MyMonad

-- NONDETERMINISTIC COMPUTATIONS
-- Examples
guard :: MonadFail m => Bool -> m ()
guard True  = skip
guard False = fail

assert :: (a -> Bool) -> [a] -> [a]
assert p mx = do {x <- mx; guard (p x); return x}

-- Permutations
select :: [a] -> [(a,[a])]
select []     = fail
select (x:xs) = sq (return (x,xs)) (do {(y,ys) <- select xs; return (y,x:ys)})

perms :: [a] -> [[a]]
perms [] = return []
perms xs = do {(y,ys) <- select xs; zs <- perms ys; return (y:zs)}