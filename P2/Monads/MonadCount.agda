module Monads.MonadCount where

open import Abel.Category.Monad
open import Monads.Exponentiation

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


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
  -- _>>_ Mon (_>>_ Mon (hanoi Mon n) (skip Mon)) (hanoi Mon n)


open Relation.Binary.PropositionalEquality.≡-Reasoning
{-
prop1 : {M : Set → Set} (Mon : Monad M) (mx : M ⊤) → rep Mon 1 mx ≡ mx
prop1 Mon mx =
  begin
    rep Mon 1 mx ≡⟨ refl ⟩
    bind Mon (λ _ → return Mon tt) mx ≡⟨ refl ⟩
    bind Mon (λ tt → return Mon tt) mx ≡⟨ refl ⟩
    bind Mon (return Mon) mx ≡⟨ unity-right mx ⟩
    mx
  ∎
-}

prop2 : {M : Set → Set} (Mon : Monad M) (mx : M ⊤) (m n : ℕ) → 
      rep Mon (m + n) mx ≡ _>>_  Mon (rep Mon m mx) (rep Mon n mx)
prop2 Mon mx zero n =
  begin
    rep Mon (zero + n) mx ≡⟨ refl ⟩
    _>>_ Mon mx (rep Mon (zero + n) mx) ≡⟨ ? ⟩
    _>>_ Mon (rep Mon zero mx) (rep Mon n mx)
  ∎

prop2 Mon mx (suc m) n =
  begin
    rep Mon ((suc m) + n) mx ≡⟨ ? ⟩
    _>>_ Mon (rep Mon (suc m) mx) (rep Mon n mx)
  ∎

{-
test : {M : Set → Set} (Mon : Monad M) (n : ℕ) → 
       (hanoi Mon n) ≡ (rep Mon ((2 ^ n) ∸ 1) (skip Mon))
test Mon zero    = refl
test Mon (suc n) = 
  begin
    hanoi Mon (suc n) ≡⟨ ? ⟩
    _>>_ Mon (hanoi Mon n) (_>>_ Mon (skip Mon) (hanoi Mon n)) ≡⟨ ? ⟩
    rep Mon ((2 ^ 1) ∸ 1) (skip Mon)
  ∎
-}