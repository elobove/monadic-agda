import Prelude hiding (Monad, return, fail, catch)
import MyMonad

-- FAILURE
class Monad m => MonadFail m where
  fail :: m a

instance MonadFail [] where
  fail = []
  
-- EXCEPTION
class MonadFail m => MonadExcept m where
  catch :: m a -> m a -> m a
  catch m h = if m == fail then h else m
  catch m fail = m
  
fastprod :: MonadExcept m => [Int] -> m Int
fastprod xs = catch (work xs) (return 0)

work :: [Int] -> [Int]
work xs = if (pert 0 xs) then fail else return (product xs)

pert :: Eq a => a -> [a] -> Bool
pert _ [] = False
pert x (y:ys) = (x == y) || (pert x ys)