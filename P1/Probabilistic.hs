{-# LANGUAGE FlexibleContexts #-}
module Probabilistic where

import System.Random
import System.Environment

-- PROBABILISTIC COMPUTATIONS
main :: IO ()
main = do
    g <- newStdGen
    putStrLn "What is your strategy?"
    strategy <- getLine
    if strategy == "switch"
      then print (play g switch)
      else if strategy == "stick"
           then print (play g stick)
           else putStrLn "This is not a strategy"

class Monad m => MonadProb m where
  choice :: MonadProb m => Double -> Double -> m b -> m b -> m b

instance MonadProb [] where
  choice p rand x y = if rand <= p then x else y

length1 :: Fractional b => [a] -> b
length1 = foldr (\x -> (+) 1.0) 0.0

-- Discrete uniform distribution
uniform :: [a] -> Double -> [a]
uniform [x] _ = return x
uniform (x:xs) rand =
  choice (1/length1 (x:xs)) rand (return x) (uniform xs rand)

-- THE MONTY HALL PROBLEM
data Door = A | B | C deriving (Eq, Show)

doors :: [Door]
doors = [A,B,C]

-- Hide the car behind one door ramdonly
hide :: Double -> [Door]
hide = uniform doors

-- Select one door ramdonly
pick :: Double -> [Door]
pick = uniform doors

-- Relative complement
(\/) :: Eq a => [a] -> [a] -> [a]
[] \/ _ = []
x \/ y = [a | a <- x, a `notElem` y]

-- Open one door to reveal a goat
tease :: Door -> Door -> Double -> [Door]
tease h p = uniform $ doors \/ [h,p]

-- Switch the original choice
switch :: Door -> Door -> [Door]
switch p t = return $ head (doors \/ [p,t])

-- Preserve the original choice
stick :: Door -> Door -> [Door]
stick p t = return p

play :: StdGen -> (Door -> Door -> [Door]) -> [Bool]
play g strategy = do
  let  (r1,g1) = random g
       (r2,g2) = random g1
       (r3,_)  = random g2
  h <- hide r1
  p <- pick r2
  t <- tease h p r3
  s <- strategy p t
  return (s == h)

-- Cartesian Product
cp :: [a] -> [b] -> [(a,b)]
cp x y = [(a,b) | a <- x, b <- y]

play2 :: StdGen -> (Door -> Door -> [Door]) -> [Bool]
play2 g strategy = do
  let (r1,g1) = random g
      (r2,_)  = random g1
  (h,p) <- uniform (cp doors doors) r1
  t     <- tease h p r2
  s     <- strategy p t
  return (s == h)
