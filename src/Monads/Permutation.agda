------------------------------------------------------------------------------
-- | Permutation: Example of a nondeterministic program
------------------------------------------------------------------------------

open import Abel.Category.Monad
open import Monads.MonadNonDet

module Monads.Permutation
  {M   : Set → Set}
  {Mm  : Monad'' M}
  (Mnd : MonadNonDet Mm)
  where

open import Data.List
open import Monads.Data.Tuple

open Monad'' Mm
open MonadNonDet Mnd


-- | Takes a list and nondeterministically chooses an element,
-- | returning that element and the remaining list; it fails on the empty list
select : {A : Set} → List A → M (A x (List A))
select []       = fail
select (x ∷ xs) = return ⟨ x , xs ⟩ □
  bind (λ ⟨ y , ys ⟩ → return ⟨ y , (x ∷ ys) ⟩) (select xs)

-- | Nondeterministically generates a permutation of a (finite) list
perms : {A : Set} → List A → M (List A)
perms [] = return []
perms xs =
  select xs >>= λ ⟨ y , ys ⟩ → (perms ys >>= (λ zs → return (y ∷ zs)))
