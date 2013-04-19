module Monads.MonadCount where

open import Abel.Category.Monad
open import Monads.Exponentiation

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


------------------------------------------------------------------
-- MonadCount

record MonadCount {M : Set → Set} (monad : Monad M) : Set₁ where

  constructor
    mkMonadCount

  open Monad monad

  field
    tick : M ⊤

open Monad

skip : {M : Set → Set} → Monad M → M ⊤
skip Mon = return Mon tt

rep : {M : Set → Set} →  Monad M → ℕ → M ⊤ → M ⊤
rep Mon zero    mx = skip Mon
rep Mon (suc n) mx = _>>_ Mon (mx) (rep Mon n mx)

hanoi : {M : Set → Set} →  Monad M →  ℕ → M ⊤
hanoi Mon zero    = skip Mon 
hanoi Mon (suc n) = 
  _>>_ Mon (hanoi Mon n) (_>>_ Mon (skip Mon) (hanoi Mon n))


open Relation.Binary.PropositionalEquality.≡-Reasoning


p1 : {M : Set → Set} (Mon : Monad M) (mx : M ⊤) → rep Mon 1 mx ≡ mx
p1 Mon mx = refl

{-
prop1 : {M : Set → Set} (Mon : Monad M) (mx : M ⊤) → rep Mon 1 mx ≡ mx
prop1 Mon mx = rep Mon 1 mx ≡⟨ rep Mon (suc zero) mx ⟩
               _>>_ Mon mx (rep Mon zero mx) ≡⟨ rep Mon zero mx ⟩
               _>>_ Mon mx (skip Mon) ∎
-}

{-
p2 : {M : Set → Set}  {mx : M ⊤} (Mon : Monad M) (m n : ℕ) → 
     rep Mon (m + n) mx ≡ (_>>_  Mon (rep Mon m mx) (rep Mon n mx))
p2 Mon m n = refl
-}

{-
test : {M : Set → Set} {mx : M ⊤} (Mon : Monad M) (n : ℕ) → 
       (hanoi Mon n) ≡ (rep Mon ((2 ^ n) ∸ 1) mx)
test Mon zero    = refl
test Mon (suc n) = step Mon (test Mon n)
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

    step : {M : Set → Set} (Mon : Monad M) →
           hanoi Mon n ≡ rep Mon ((2 ^ n) ∸ 1) (skip Mon) → 
           hanoi Mon (n + 1) ≡ rep Mon ((2 ^ (n + 1)) ∸ 1) (skip Mon)
    step Mon =
      begin
        _>>_ Mon (hanoi Mon n) (_>>_ Mon (skip Mon) (hanoi Mon n))
          -- ≡⟨ hanoi Mon (suc n) ⟩
          ≡⟨  ⟩
        _>>_ Mon (rep Mon ((2 ^ n)  ∸ 1) (skip Mon)) 
        (_>>_ Mon (skip Mon) (rep Mon ((2 ^ n)  ∸ 1) (skip Mon))
          ≡⟨ p1 Mon (skip Mon) ⟩
        _>>_ Mon (rep Mon ((2 ^ n)  ∸ 1) (skip Mon))
        (_>>_ Mon (rep Mon 1 (skip Mon) (rep Mon ((2 ^ n) ∸ 1) (skip Mon))
          ≡⟨ p2 Mon ((2 ^ n)  ∸ 1)) 1 (skip Mon) ⟩
        _>>_ Mon (rep Mon ((2 ^ n)  ∸ 1 + 1) (skip Mon))
        (rep Mon ((2 ^ n)  ∸ 1) (skip Mon))
          ≡⟨ p2 ((2 ^ n)  ∸ 1 + 1) 1 (skip Mon) ⟩
        rep Mon ((2 ^ n) ∸ 1 + 1 + (2 ^ n)  ∸ 1) (skip Mon)
          ≡⟨ ⟩
        rep Mon ((2 ^ n) + (2 ^ n ) ∸ 1 + 1 ∸ 1) (skip Mon) 
          ≡⟨ ⟩
        rep Mon ((2 ^ (n + 1))  ∸ 1 + 1  ∸ 1) (skip Mon)
          ≡⟨ ⟩
        rep Mon ((2 ^ (n + 1))  ∸ 1) (skip Mon) ∎
-}