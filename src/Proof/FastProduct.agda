------------------------------------------------------------------------------
-- | Fast Product: An exception example. Multiplies the elements of a list of
-- | integers, but raises an exception if it finds a zero, subsequently
-- | catching the exception and returning zero for the overall product
------------------------------------------------------------------------------

open import Abel.Category.Monad
open import Proof.MonadNonDet
open import Proof.MonadExcept

module Proof.FastProduct
  {M   : Set → Set}
  {Mm  : Monad'' M}
  {Mnd : MonadNonDet Mm}
  (Me  : MonadExcept Mnd)
  where

open import Data.Integer
open import Data.List
open import Data.Bool hiding (_≟_)
open import Data.Bool.Properties
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality.Core using (sym)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Monad''     Mm
open MonadNonDet Mnd
open MonadExcept Me
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- | Boolean equality for Integers
_==_ : ℤ → ℤ → Bool
i₁ == i₂ = ⌊ i₁ ≟ i₂ ⌋

-- | Integer zero
0ℤ : ℤ
0ℤ = ℤ.pos 0

--| Integer one
1ℤ : ℤ
1ℤ = ℤ.pos 1

-- | Checks if an integer is on a list of integers
elem : ℤ → List ℤ → Bool
elem x []        = false
elem x (y ∷ ys) = if (x == y) then true else (elem x ys)

-- | Computes the product of a list of integers
productℤ : List ℤ → ℤ
productℤ = foldl _*_ 1ℤ

work : List ℤ → M ℤ
work xs = if (elem 0ℤ xs) then fail else (return (productℤ xs))

fastProd : List ℤ → M ℤ
fastProd xs = catch (work xs) (return 0ℤ)

--| Pop an if_then_else_ statement from a parameter of a function
pop-if :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) x {y z w} →
  f (if x then y else z) w ≡ (if x then (f y w) else (f z w))
pop-if _ true  = refl
pop-if _ false = refl

-- | Proof: fastProduct is pure
pureFastProd : (xs : List ℤ) → fastProd xs ≡ return (productℤ xs)
pureFastProd xs =
  begin
    catch (work xs) (return 0ℤ)
      ≡⟨ cong (λ x → catch x (return 0ℤ)) refl ⟩
    catch (if (elem 0ℤ xs) then fail else (return (productℤ xs))) (return 0ℤ)
      ≡⟨ pop-if catch (elem 0ℤ xs) ⟩
    (if (elem 0ℤ xs) then mx else my)
      ≡⟨ cong (λ x → (if (elem 0ℤ xs) then x else my))
               (catch-fail₁ (return 0ℤ)) ⟩
    (if (elem 0ℤ xs) then (return 0ℤ) else my)
      ≡⟨ cong (λ x → (if (elem 0ℤ xs) then (return 0ℤ) else x))
               (catch-return (productℤ xs) (return 0ℤ)) ⟩
    (if (elem 0ℤ xs) then (return 0ℤ) else (return (productℤ xs)))
      ≡⟨ sym (push-function-into-if return (elem 0ℤ xs)) ⟩
    return (if (elem 0ℤ xs) then 0ℤ else (productℤ xs))
      ≡⟨ cong (λ x → return x) {!!} ⟩
    return (productℤ xs)
  ∎
    where mx = catch fail (return 0ℤ)
          my = catch (return (productℤ xs)) (return 0ℤ)
