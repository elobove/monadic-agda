------------------------------------------------------------------------------
-- | Fast Product: An exception example. Multiplies the elements of a list of
-- | natural numbers, but raises an exception if it finds a zero, subsequently
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

open import Data.Nat
open import Data.Nat.Properties.Simple
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

-- | Boolean equality for Natural numbers
_==_ : ℕ → ℕ → Bool
i₁ == i₂ = ⌊ i₁ ≟ i₂ ⌋

-- | Checks if a number is on a list
elem : ℕ → List ℕ → Bool
elem x []        = false
elem x (y ∷ ys) = if (x == y) then true else (elem x ys)

-- | Computes the product of a list of Natural numbers
productℕ : List ℕ → ℕ
productℕ []        = 1
productℕ (x ∷ xs) = x * productℕ xs

-- | If the product of the list is zero then the product of that list with a new
-- | element is still zero
product0₁ : ∀ n → (xs : List ℕ) → (productℕ xs) ≡ 0 → (productℕ (n ∷ xs)) ≡ 0
product0₁ n xs eq =
  begin
    n * productℕ xs ≡⟨ cong (λ y → n * y) eq ⟩
    n * 0            ≡⟨ *-comm n 0 ⟩
    0
  ∎

-- | If there is a zero on a list its product is zero
product0₂ : (xs : List ℕ) → (elem 0 xs) ≡ true → (productℕ xs) ≡ 0
product0₂ []               = λ ()
product0₂ (zero ∷ xs)  eq = refl
product0₂ (suc n ∷ xs) eq = product0₁ (suc n) xs (product0₂ xs eq)

if-cong : {a c d : ℕ} {b : Bool} → (b ≡ true → a ≡ d) →
          (b ≡ false → c ≡ d) → (if b then a else c) ≡ d
if-cong {b = true } t _ = t refl
if-cong {b = false} _ f = f refl

--| Pop an if statement from a parameter of a function
pop-if :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) x {y z w} →
  f (if x then y else z) w ≡ (if x then (f y w) else (f z w))
pop-if _ true  = refl
pop-if _ false = refl

-- | Proof: fastProduct is pure
work : List ℕ → M ℕ
work xs = if (elem 0 xs) then fail else (return (productℕ xs))

fastProd : List ℕ → M ℕ
fastProd xs = catch (work xs) (return 0)

pureFastProd : (xs : List ℕ) → fastProd xs ≡ return (productℕ xs)
pureFastProd xs =
  begin
    catch (if (elem 0 xs) then fail else (return (productℕ xs))) (return 0)
      ≡⟨ pop-if catch (elem 0 xs) ⟩
    (if (elem 0 xs) then mx else my)
      ≡⟨ cong (λ x → (if (elem 0 xs) then x else my))
               (catch-fail₁ (return 0)) ⟩
    (if (elem 0 xs) then (return 0) else my)
      ≡⟨ cong (λ x → (if (elem 0 xs) then (return 0) else x))
               (catch-return (productℕ xs) (return 0)) ⟩
    (if (elem 0 xs) then (return 0) else (return (productℕ xs)))
      ≡⟨ sym (push-function-into-if return (elem 0 xs)) ⟩
    return (if (elem 0 xs) then 0 else (productℕ xs))
      ≡⟨ cong return extra-if ⟩
    return (productℕ xs)
  ∎
    where mx       = catch fail (return 0)
          my       = catch (return (productℕ xs)) (return 0)
          extra-if = if-cong (λ p → sym (product0₂ xs p)) (λ _ → refl)
