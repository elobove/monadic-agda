module Monads.MonadNonDet where

open import Abel.Category.Monad
open import Abel.Category.Applicative
open import Abel.Category.Functor

open import Data.List
open import Data.Tuple
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------
-- MonadFail

record MonadFail (M : Set → Set) {monad : Monad M} : Set₁ where
  constructor
    mkMonadFail

  open Monad monad

  field
    fail : ∀{A} → M A

    fail-zero-seq : ∀{A} (m : M A) → fail >> m ≡ fail

------------------------------------------------------------------
-- MonadAlt

record MonadAlt (M : Set → Set) {monad : Monad M} : Set₁ where
  constructor
    mkMonadAlt

  open Monad monad

  field
    _□_ : ∀ {A} → M A → M A → M A

    choice-assoc : ∀ {A} (m : M A) (n : M A) (p : M A) →
                   (m □ n) □ p ≡ m □ (n □ p)

    choice-∘     : ∀ {A B} (m : M A) (n : M A) (k : A → M B) →
                   (m □ n) >>= k ≡ (m >>= k) □ (n >>= k)

------------------------------------------------------------------
-- MonadNonDet

record MonadNonDet (M : MonadFail MonadAlt) : Set₁ where
  constructor
    mkMonadNonDet

select : {M : MonadNonDet} {A : Set} → List A → M <A , (List A)>
select []       = fail
select (x ∷ xs) = 
  return (x, xs) □ (select xs >>= (λ <y , ys> → return <y , (x ∷ ys)>))

perms : {M : MonadNonDet} {A : Set} → List A → M (List A)
perms [] = return []
perms xs = 
  select xs >>= λ <y , ys> → (perms ys >>= (λ zs → return (y ∷ zs)))