module Monads.Exponentiation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat

_^_ : ℕ → ℕ → ℕ
x ^ zero    = 1
x ^ (suc n) = x * (x ^ n)

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Symmetry
sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Right identity for addition
+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero    = refl
+-rightIdentity (suc n) = cong suc ( +-rightIdentity n)

-- Rigth identity for multiplication
*-rightIdentity : ∀ n → n * 1 ≡ n
*-rightIdentity  zero   = refl
*-rightIdentity (suc n) = cong suc (*-rightIdentity n)

-- Rigth identity for exponentiation
^-rightIdentity : ∀ n → n ^ 1 ≡ n
^-rightIdentity zero    = refl
^-rightIdentity (suc n) = *-rightIdentity (suc n)

x+Sy≡S[x+y] : ∀ m n → m + suc n ≡ suc (m + n)
x+Sy≡S[x+y] zero    n  = refl
x+Sy≡S[x+y] (suc m) n = cong suc (x+Sy≡S[x+y] m n)

-- Commutative property of addition
+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-rightIdentity n)
+-comm (suc m) n =
  begin
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + suc m
  ∎

-- Associative property of addition
+-assoc : ∀ m n p → m + (n + p) ≡ (m + n) + p
+-assoc zero    _ _ = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

succ : ∀ n → suc n ≡ n + 1
succ zero    = refl
succ (suc n) = cong suc (succ n)

-- Distributive property
left-dist : ∀ m n p → m * (n + p) ≡ m * n + m * p
left-dist zero    _ _ = refl
left-dist (suc m) n p =
  begin
    (n + p) + m * (n + p)
      ≡⟨ cong (λ x → (n + p) + x) (left-dist m n p) ⟩
    (n + p) + (m * n + m * p)
      ≡⟨ cong (λ x → x + (m * n + m * p)) (+-comm n p) ⟩
    (p + n) + (m * n + m * p)
      ≡⟨ +-assoc (p + n) (m * n) (m * p)⟩
    ((p + n) + m * n) + m * p
      ≡⟨ cong (λ x → x + m * p) (sym (+-assoc p n (m * n))) ⟩
    (p + (suc m * n)) + m * p
      ≡⟨ cong (λ x → x + m * p) (+-comm p (suc m * n))  ⟩
    ((suc m * n) + p) + m * p
      ≡⟨ sym (+-assoc (suc m * n) p (m * p)) ⟩
    suc m * n + suc m * p
  ∎

2n≡n+n : ∀ n → 2 * n ≡ n + n
2n≡n+n zero    = refl
2n≡n+n (suc n) =
  begin
    suc n + (suc n + zero) ≡⟨ +-assoc (suc n) (suc n) zero ⟩
    (suc n + suc n) + zero ≡⟨ +-comm (suc n + suc n) zero ⟩
    suc n + suc n
  ∎

p1 : ∀ n → n ^ 2 ≡ n * n
p1 zero    = refl
p1 (suc n) = cong (λ x → suc n * x) (*-rightIdentity (suc n))

p2 : ∀ n → (2 ^ n) + (2 ^ n) ≡ 2 ^ (n + 1)
p2 zero    = refl
p2 (suc n) =
  begin
    (2 ^ suc n) + (2 ^ suc n) ≡⟨ sym (2n≡n+n (2 ^ suc n)) ⟩
    2 ^ (suc (suc n))         ≡⟨ cong (λ x → 2 ^ x) (succ (suc n)) ⟩
    2 ^ (suc n + 1)
  ∎

-- +∸-assoc : ∀ m n p → m + (suc n ∸ p) ≡ (m + suc n) ∸ p
-- +∸-assoc zero    _ _ = refl
-- +∸-assoc (suc m) n p =
--   begin
--     suc m + (suc n ∸ p) ≡⟨ refl ⟩
--     suc (m + (suc n ∸ p)) ≡⟨ cong suc (+∸-assoc m n p) ⟩
--     suc ((m + suc n) ∸ p) ≡⟨ {!!} ⟩
--     suc (m + suc n) ∸ p ≡⟨ refl ⟩
--     (suc m + suc n) ∸ p
--   ∎