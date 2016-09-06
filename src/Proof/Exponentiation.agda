------------------------------------------------------------------------------
-- | Exponentiation: Mathematical operation
------------------------------------------------------------------------------

module Proof.Exponentiation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat
open import Data.Bool
open import Data.Nat.Properties
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)

-- | Exponentiation operation
_^_ : ℕ → ℕ → ℕ
x ^ zero    = 1
x ^ (suc n) = x * (x ^ n)

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- | Symmetry
sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- | Right identity for addition
+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero    = refl
+-rightIdentity (suc n) = cong suc ( +-rightIdentity n)

-- | Rigth identity for multiplication
*-rightIdentity : ∀ n → n * 1 ≡ n
*-rightIdentity  zero   = refl
*-rightIdentity (suc n) = cong suc (*-rightIdentity n)

-- | Rigth identity for exponentiation
^-rightIdentity : ∀ n → n ^ 1 ≡ n
^-rightIdentity zero    = refl
^-rightIdentity (suc n) = *-rightIdentity (suc n)

x+Sy≡S[x+y] : ∀ m n → m + suc n ≡ suc (m + n)
x+Sy≡S[x+y] zero    n  = refl
x+Sy≡S[x+y] (suc m) n = cong suc (x+Sy≡S[x+y] m n)

-- | Commutative property of addition
+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-rightIdentity n)
+-comm (suc m) n =
  begin
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + suc m
  ∎

-- | Associative property of addition
+-assoc : ∀ m n p → m + (n + p) ≡ (m + n) + p
+-assoc zero    _ _ = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

-- | Distributive property
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

-- | Rewrite suc n
succ : ∀ n → suc n ≡ n + 1
succ zero    = refl
succ (suc n) = cong suc (succ n)

2n≡n+n : ∀ n → 2 * n ≡ n + n
2n≡n+n zero    = refl
2n≡n+n (suc n) =
  begin
    suc n + (suc n + zero) ≡⟨ +-assoc (suc n) (suc n) zero ⟩
    (suc n + suc n) + zero ≡⟨ +-comm (suc n + suc n) zero ⟩
    suc n + suc n
  ∎

suc-^ : ∀ n → (2 ^ n) + (2 ^ n) ≡ 2 ^ (n + 1)
suc-^ zero    = refl
suc-^ (suc n) =
  begin
    (2 ^ suc n) + (2 ^ suc n) ≡⟨ sym (2n≡n+n (2 ^ suc n)) ⟩
    2 ^ (suc (suc n))         ≡⟨ cong (λ x → 2 ^ x) (succ (suc n)) ⟩
    2 ^ (suc n + 1)
  ∎

n≡m→n≤m : ∀ n {m} → n ≡ m → n ≤ m
n≡m→n≤m zero    refl = z≤n
n≡m→n≤m (suc n) refl = s≤s (n≡m→n≤m n refl)

1≤2^n : ∀ n → 1 ≤ (2 ^ n)
1≤2^n zero    = s≤s z≤n
1≤2^n (suc n) =
  start
    1
      ≤⟨ 1≤2^n n ⟩
    (2 ^ n)
      ≤⟨ n≤m+n (2 ^ n) (2 ^ n) ⟩
    (2 ^ n) + (2 ^ n)
      ≤⟨ n≡m→n≤m ((2 ^ n) + (2 ^ n)) (suc-^ n) ⟩
    2 ^ (n + 1)
      ≤⟨ n≡m→n≤m (2 ^ (n + 1)) (cong (λ x → 2 ^ x) (sym (succ n))) ⟩
    2 ^ (suc n)
  □

thm : ∀ n → 2 ^ (n + 1) ∸ 1 ≡ ((2 ^ n) ∸ 1) + 1 + ((2 ^ n) ∸ 1)
thm n =
  begin
    2 ^ (n + 1) ∸ 1
      ≡⟨ cong (λ x → x ∸ 1) (sym (suc-^ n)) ⟩
    (2 ^ n) + (2 ^ n) ∸ 1
      ≡⟨ +-∸-assoc (2 ^ n) (1≤2^n n) ⟩
    (2 ^ n) + ((2 ^ n) ∸ 1)
      ≡⟨ +-comm (2 ^ n) ((2 ^ n) ∸ 1) ⟩
    ((2 ^ n) ∸ 1) + (2 ^ n)
      ≡⟨ cong (λ x → ((2 ^ n) ∸ 1) + x) (sym (m+n∸n≡m (2 ^ n) 1)) ⟩
    ((2 ^ n) ∸ 1) + ((2 ^ n) + 1 ∸ 1)
      ≡⟨ cong (λ x → ((2 ^ n) ∸ 1) + (x ∸ 1)) (+-comm (2 ^ n) 1) ⟩
    ((2 ^ n) ∸ 1) + (1 + (2 ^ n) ∸ 1)
      ≡⟨ cong ((λ x → ((2 ^ n) ∸ 1) + x)) (+-∸-assoc 1 (1≤2^n n)) ⟩
    ((2 ^ n) ∸ 1) + (1 + ((2 ^ n) ∸ 1))
      ≡⟨ +-assoc (((2 ^ n) ∸ 1)) 1 (((2 ^ n) ∸ 1)) ⟩
    ((2 ^ n) ∸ 1) + 1 + ((2 ^ n) ∸ 1)
  ∎

-- | Some extra properties
n^2≡n*n : ∀ n → n ^ 2 ≡ n * n
n^2≡n*n zero    = refl
n^2≡n*n (suc n) = cong (λ x → suc n * x) (*-rightIdentity (suc n))

p1-dif : ∀ q n m → (q + n) ∸ (q + m) ≡ n ∸ m
p1-dif zero    n m = refl
p1-dif (suc k) n m = cong (λ x → x) (p1-dif k n m)

Sm≤Sn→m≤n : ∀ {m n} → suc m ≤ suc n → m ≤ n
Sm≤Sn→m≤n le = cancel-+-left-≤ (suc zero) le

-- | Split rule of Natural number subtraction
diffSplit : ∀ (P : ℕ → Set) → (m n : ℕ) → (m < n → P 0) →
            (∀ (p : ℕ) → m ≡ n + p → P p) → P (m ∸ n)
diffSplit P zero    zero    _  pN = pN zero refl
diffSplit P zero    (suc m) p0 _  = p0 (s≤s z≤n)
diffSplit P (suc n) zero    p0 pN = pN (suc n) refl
diffSplit P (suc n) (suc m) p0 pN =
  diffSplit P n m (λ z → p0 (s≤s z)) (λ p z → pN p (cong suc z))
