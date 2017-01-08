------------------------------------------------------------------------------
-- | Towers of Hanoi: A counter example
------------------------------------------------------------------------------

open import Proof.Monad
open import Proof.MonadCount

module Proof.Hanoi
  {M  : Set → Set}
  {Mm : Monad M}
  (Mc : MonadCount Mm)
  where

open import Data.Nat
open import Data.Unit
open import Proof.Exponentiation
open import Relation.Binary.PropositionalEquality.Core using (sym)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Monad      Mm
open MonadCount Mc

-- | Solves the Towers of Hanoi problem. It ticks the counter once for
-- | each move of a disc
hanoi : ℕ → M ⊤
hanoi zero    = skip
hanoi (suc n) = hanoi n >> tick >> hanoi n

-- | Repeats a unit computation a fixed number of times
rep :  ℕ → M ⊤ → M ⊤
rep zero    mx = skip
rep (suc n) mx = mx >> rep n mx

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- | Properties of rep
rep-1 : (mx : M ⊤) → rep 1 mx ≡ mx
rep-1 = unity-right

rep-mn : ∀ m n → (mx : M ⊤) → rep (m + n) mx ≡ (rep m mx >> rep n mx)
rep-mn zero    _ mx = sym (unity-left tt)
rep-mn (suc m) n mx =
  begin
    bind (λ _ → rep (m + n) mx) mx
      ≡⟨ cong f (rep-mn m n mx) ⟩
    bind (λ _ → bind (λ _ → rep n mx) (rep m mx)) mx
      ≡⟨ sym (associativity mx) ⟩
    (rep (suc m) mx >> rep n mx)
  ∎
    where f = λ x → bind (λ _ → x) mx

-- | Verification of hanoi
moves : ∀ n → hanoi n ≡ rep (2 ^ n ∸ 1) tick
moves zero    = refl
moves (suc n) =
  begin
    (hanoi n >> tick >> hanoi n)
      ≡⟨ cong f (moves n) ⟩
    (rep (2 ^ n ∸ 1) tick >> tick >> rep (2 ^ n ∸ 1) tick)
      ≡⟨ cong g (sym (rep-1 tick)) ⟩
    (rep (2 ^ n ∸ 1) tick >> rep 1 tick >> rep (2 ^ n ∸ 1) tick)
      ≡⟨ cong (λ x → x >> r) (sym (rep-mn (2 ^ n ∸ 1) 1 tick)) ⟩
    (rep (2 ^ n ∸ 1 + 1) tick >> rep (2 ^ n ∸ 1) tick)
      ≡⟨ sym (rep-mn (2 ^ n ∸ 1 + 1) (2 ^ n ∸ 1) tick) ⟩
    rep ((2 ^ n ∸ 1) + 1 + (2 ^ n ∸ 1)) tick
      ≡⟨ cong (λ x → rep x tick) (sym (thm n)) ⟩
    rep (2 ^ (n + 1) ∸ 1) tick
      ≡⟨ cong (λ x → rep (2 ^ x ∸ 1) tick) (sym (succ n)) ⟩
    rep (2 ^ (suc n) ∸ 1) tick
  ∎
    where f = λ x → x >> tick >> x
          r = rep (2 ^ n ∸ 1) tick
          g = λ x → r >> x >> r
