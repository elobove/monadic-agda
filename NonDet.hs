module NonDet where

import Control.Monad

-- NONDETERMINISTIC COMPUTATIONS

-- Select an element of a list
select :: [a] -> [(a,[a])]
select []     = mzero
select (x:xs) = mplus (return (x,xs)) aux
  where aux = do {(y,ys) <- select xs; return (y,x:ys)}

-- Permute a finite list
perms :: [a] -> [[a]]
perms [] = return []
perms xs =
  do {(y,ys) <- select xs; zs <- perms ys; return (y:zs)}
