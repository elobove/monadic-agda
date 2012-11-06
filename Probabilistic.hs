{-# LANGUAGE FlexibleContexts #-}

import MyMonad
import Prelude hiding (Monad,return)
import System.Random
import System.Environment

main :: IO()
main = do
    g <- newStdGen
    putStrLn "¿Cual es tu estrategia?"
    strategy <- getLine
    if strategy == "switch"
      then print (play g switch)
           else if strategy == "stick"
                   then print (play g switch)
                        else putStrLn "Eso no es una estrategia! ¬¬"

-- Standard normal distribution
std :: Double -> Double
std x = (exp((-x^2)/2)/sqrt(4*pi))

class Monad m => MonadProb m where
  choice :: (MonadProb m) => Double -> Double -> m b -> m b -> m b

instance MonadProb [] where
  choice p real x y = if p < (std real) then y else x

length1 :: Fractional b => [a] -> b
length1 [] = 0.0
length1 (x:xs) = 1.0 + (length1 xs)

uniform :: [a] -> Double -> [a]
uniform [x] _ = return x
uniform (x:xs) real = choice (1/length1 (x:xs)) real (return x) (uniform xs real)

-- THE MONTY HALL PROBLEM
data Door = A | B | C deriving (Eq, Show)

doors :: [Door]
doors = [A,B,C]

-- Hiding the car behind one door ramdonly
hide :: Double -> [Door]
hide x = uniform doors x

-- Selecting one door ramdonly
pick :: Double -> [Door]
pick x = uniform doors x

(\/) :: Eq a => [a] -> [a] -> [a]
[] \/ _ = []
x \/ y = [a | a <- x, a `notElem` y]

-- Opening one door to reveal a goat
tease :: Door -> Door -> Double -> [Door]
tease h p real = uniform (doors \/ [h,p]) real

-- Switching the original choice
switch :: Door -> Door -> [Door]
switch p t = return (head (doors \/ [p,t]))

-- Staying in the original choice
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

{-
-- Cartesian Product
cp :: [a] -> [b] -> [(a,b)]
cp x y = [(a,b) | a <- x, b <- y]

play2 :: (Door -> Door -> [Door]) -> [Bool]
play2 strategy = do
  (h,p) <- uniform (cp doors doors)
  t <- tease h p
  s <- strategy p t
  return (s == h)
-}
