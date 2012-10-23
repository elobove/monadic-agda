{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
module Stateful where

import NonDet
import Control.Monad.State hiding (guard)
{-
class Monad m => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()
-}

type Square a = (a,a)

-- Purely functional implementation
square :: (a -> b) -> Square a -> Square b
square f (a,b) = (f a, f b)

test :: Square Int -> Square [Int] -> (Bool,Square [Int])
test (c,r) (ups,downs) =
  ((u `notElem` ups) && (d `notElem` downs),(u:ups,d:downs))
  where (u,d) = (r-c,r+c)

safe1 :: Square [Int] -> [Square Int] -> (Bool,Square [Int])
safe1 = foldr step1 . start1

start1 :: Square [Int] -> (Bool, Square [Int])
start1 updowns = (True,updowns)

step1 :: Square Int -> (Bool,Square [Int]) -> (Bool,Square [Int])
step1 cr (restOK,updowns) =
  (thisOK && restOK,updowns')
  where (thisOK,updowns') = test cr updowns

-- Nondeterministic implementation
queens :: Int -> [[Int]]
queens n = do
  rs <- perms[1..n]
  guard (fst(safe1 empty (place n rs)))
  return rs

place n rs = zip [1..n] rs
empty = ([],[])

-- Statefully implementation
safe2 :: MonadState (Square [Int]) m => [Square Int] -> m Bool
safe2 = foldr step2 start2

start2 :: MonadState (Square [Int]) m => m Bool
start2 = return True

step2 :: MonadState (Square [Int]) m => Square Int -> m Bool -> m Bool
step2 cr k = do
  b' <- k
  uds <- get
  let (b,uds') = test cr uds
  put uds'
  return (b && b')

-- run :: MonadState (Square [Int]) m => m Bool -> Square [Int] ->
--       (Bool, Square [Int])

test10 :: [Square Int] -> Square [Int] -> Bool
test10 crs updowns = runState (safe2 crs) updowns == safe1 updowns crs
