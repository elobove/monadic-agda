{-# LANGUAGE FlexibleContexts #-}
import System.Random
import System.Environment

-- PROBABILISTIC COMPUTATIONS
main :: IO ()
main = do
  g <- newStdGen
  putStrLn "What is your strategy?"
  strategy <- getLine
  if strategy == "switch"
    then print (play2 g switch)
    else if strategy == "stick"
         then print (play2 g stick)
         else putStrLn "This is not a strategy"

class Monad m => MonadProb m where
  choice ::  Double -> m a -> m a -> m a

data Dist a = Return a | Choice Double (Dist a) (Dist a)
            deriving Show

instance Monad Dist where
  return             = Return
  Return x     >>= f = f x
  Choice w p q >>= f = Choice w (p >>= f) (q >>= f)

instance MonadProb Dist where
  choice = Choice

length1 :: Fractional b => [a] -> b
length1 = foldr (\x -> (+) 1.0) 0.0

-- Discrete uniform distribution
uniform :: [a] -> Dist a
uniform [x]    = return x
uniform (x:xs) =
  choice (1/length1 (x:xs)) (return x) (uniform xs)

-- THE MONTY HALL PROBLEM
data Door = A | B | C deriving (Eq, Show)

doors :: [Door]
doors = [A,B,C]

-- Hide the car behind one door ramdonly
hide :: Dist Door
hide = uniform doors

-- Select one door ramdonly
pick :: Dist Door
pick = uniform doors

-- Relative complement
(\/) :: Eq a => [a] -> [a] -> [a]
[] \/ _ = []
x  \/ y = [a | a <- x, a `notElem` y]

-- Open one door to reveal a goat
tease :: Door -> Door -> Dist Door
tease h p = uniform $ doors \/ [h,p]

-- Switch the original choice
switch :: Door -> Door -> Dist Door
switch p t = return $ head (doors \/ [p,t])

-- Preserve the original choice
stick :: Door -> Door -> Dist Door
stick p t = return p

taKe :: Dist a -> Double -> a
taKe (Return x) _        = x
taKe (Choice w p q) rand = if rand < w
                           then taKe p rand
                           else taKe q rand

play :: StdGen -> (Door -> Door -> Dist Door) -> Dist Bool
play g strategy = do
  let  (r1,g1) = random g
       (r2,g2) = random g1
       (r3,_)  = random g2
       h       = taKe hide r1
       p       = taKe pick r2
       t       = taKe (tease h p) r3
       s       = taKe (strategy p t) 1
  return (s == h)

-- Cartesian Product
cp :: [a] -> [b] -> [(a,b)]
cp x y = [(a,b) | a <- x, b <- y]

play2 :: StdGen -> (Door -> Door -> Dist Door) -> Dist Bool
play2 g strategy = do
  let (r1,g1) = random g
      (r2,_)  = random g1
      (h,p)   = taKe (uniform (cp doors doors)) r1
      t       = taKe (tease h p) r2
      s       = taKe (strategy p t) 1
  return (s == h)