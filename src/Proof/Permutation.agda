------------------------------------------------------------------------------
-- | Permutation: Example of a nondeterministic program
------------------------------------------------------------------------------

open import Abel.Category.Monad
open import Proof.MonadNonDet
open import Data.Nat

module Proof.Permutation
  {M   : Set → Set}
  {Mm  : Monad'' M}
  (Mnd : MonadNonDet Mm)
  where

open import Data.List
open import Proof.Data.Tuple

open Monad'' Mm
open MonadNonDet Mnd


-- | Takes a list and nondeterministically chooses an element,
-- | returning that element and the remaining list; it fails on the empty list
select : {A : Set} → List A → M (A x (List A))
select []       = fail
select (x ∷ xs) = return ⟨ x , xs ⟩ □
  bind (λ ys → return ⟨ fst ys , (x ∷ snd ys) ⟩) (select xs)

-- | Nondeterministically generates a permutation of a (finite) list
perms : {A : Set} → List A → ℕ → M (List A)
perms _  zero    = return []
perms xs (suc n) =
  select xs >>= λ ys → (perms (snd ys) n >>= (λ zs → return (fst ys ∷ zs)))
