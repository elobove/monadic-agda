open import Abel.Category.Monad
open import Monads.MonadCount

module Monads.Hanoi
  {M  : Set → Set}
  {Mm : Monad M}
  (Mc : MonadCount Mm)
  where

open import Data.Nat
open import Data.Unit
open import Function using (_∘_)
open import Monads.Exponentiation
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Monad Mm

skip : M ⊤
skip = return tt

open MonadCount Mc

rep :  ℕ → M ⊤ → M ⊤
rep zero    mx = skip
rep (suc n) mx = mx >> rep n mx

hanoi : ℕ → M ⊤
hanoi zero    = skip
hanoi (suc n) = hanoi n >> tick >> hanoi n

open Relation.Binary.PropositionalEquality.≡-Reasoning

prop0 : ∀ n → n + zero ≡ n
prop0 zero    = refl
prop0 (suc n) = +-comm (suc n) zero

prop1 : (mx : M ⊤) → rep 1 mx ≡ mx
prop1 = unity-right

prop2 : ∀ m n → (mx : M ⊤) → rep (m + n) mx ≡ (rep m mx >> rep n mx)
prop2 zero    _ mx = sym (unity-left tt)
prop2 (suc m) n mx =
  begin
    bind (λ _ → rep (m + n) mx) mx
      ≡⟨ cong f (prop2 m n mx) ⟩
    bind (λ _ → bind (λ _ → rep n mx) (rep m mx)) mx
      ≡⟨ sym (associativity mx) ⟩
    (rep (suc m) mx >> rep n mx)
  ∎
    where f = λ x → bind (λ _ → x) mx

test : ∀ n → hanoi n ≡ rep ((2 ^ n) ∸ 1) tick
test zero    = refl
test (suc n) =
  begin
    hanoi (suc n)
      ≡⟨ refl ⟩
    (hanoi n >> tick >> hanoi n)
      ≡⟨ cong f (test n) ⟩
    (rep ((2 ^ n) ∸ 1) tick >> tick >> rep ((2 ^ n) ∸ 1) tick)
      ≡⟨ cong g (sym (prop1 tick)) ⟩
    (rep ((2 ^ n) ∸ 1) tick >> rep 1 tick >> rep ((2 ^ n) ∸ 1) tick)
      ≡⟨ cong (λ x → x >> r) (sym (prop2 ((2 ^ n) ∸ 1) 1 tick)) ⟩
    (rep (2 ^ n) tick >> rep ((2 ^ n) ∸ 1) tick)
      ≡⟨ sym (prop2 (2 ^ n) ((2 ^ n) ∸ 1) tick) ⟩
    rep (2 ^ n + (2 ^ n ∸ 1)) tick
      ≡⟨ ? ⟩
    rep ((2 ^ n + 2 ^ n) ∸ 1) tick
      ≡⟨ cong (λ x → rep (x ∸ 1) tick) (p2 n) ⟩
    rep ((2 ^ (n + 1)) ∸ 1) tick
      ≡⟨ cong (λ x → rep ((2 ^ x) ∸ 1) tick) (sym (succ n)) ⟩
    rep ((2 ^ (suc n)) ∸ 1) tick
  ∎
    where f = λ x → x >> tick >> x
          r = rep ((2 ^ n) ∸ 1) tick
          g = λ x → r >> x >> r