module Exception where

import Control.Monad
import Network.HTTP.Base

-- EXCEPTIONAL COMPUTATIONS
main :: IO ()
main = do
  xs <- getLine
  sol <- fastprod $ read xs
  print (sol)

-- Multiply the elements of an integer list
fastprod :: [Int] -> IO Int
fastprod xs = catchIO_ (work xs) (return 0)

work :: [Int] -> IO Int
work xs = if (0 `elem` xs)
          then mzero
          else return (product xs)