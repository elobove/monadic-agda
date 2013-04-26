module Monads.Exponentiation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat

_^_ : ℕ → ℕ → ℕ
x ^ zero    = 1
x ^ (suc n) = x * (x ^ n)

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Identity or Neutral element of multiplication
*-mod : ∀ n → n * 1 ≡ n
*-mod  zero   = refl
*-mod (suc n) = 
  begin
    suc n * 1 ≡⟨ refl ⟩
    suc (n * 1) ≡⟨ cong suc (*-mod n) ⟩
    suc n
  ∎

-- Identity or Neutral element of exponentiation
^-mod : ∀ n → n ^ 1 ≡ n
^-mod zero    = refl
^-mod (suc n) =
  begin
   (suc n) ^ 1 ≡⟨ refl ⟩
   (suc n) ^ ((suc n) ^ zero) ≡⟨ refl ⟩
   (suc n) * 1 ≡⟨ *-mod (suc n) ⟩
   (suc n)
  ∎       

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

x+Sy≡S[x+y] : ∀ m n → m + suc n ≡ suc (m + n)
x+Sy≡S[x+y] zero    n  = refl
x+Sy≡S[x+y] (suc m) n = cong suc (x+Sy≡S[x+y] m n)

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero    = refl
+-rightIdentity (suc n) = cong suc ( +-rightIdentity n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-rightIdentity n)
+-comm (suc m) n =
  begin
    suc m + n   ≡⟨ refl ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + suc m
  ∎

p : ∀ n → suc n ≡ n + 1
p zero    = refl
p (suc n) = 
  begin
    suc (suc n) ≡⟨ cong suc (p n) ⟩
    suc (n + 1) ≡⟨ refl ⟩
    (suc n) + 1
  ∎
{-
p0 : ∀ n → n + n ≡ 2 * n
p0 zero    = refl
p0 (suc n) = 
  begin
    suc n + suc n ≡⟨ refl ⟩
    suc (n + suc n) ≡⟨ cong suc (+-comm n (suc n)) ⟩
    suc (suc n + n) ≡⟨ refl ⟩
    --suc (suc (n + n)) ≡⟨ cong (λ x → suc (suc x)) (p0 n) ⟩
   -- suc (suc (2 * n)) ≡⟨ cong suc (p (2 * n)) ⟩
   -- suc (2 * n + 1) ≡⟨ p (2 * n + 1) ⟩  
   -- 2 * n + 1 + 1 ≡⟨  refl ⟩
   -- 2 * n + 2 ≡⟨ {!!} ⟩
    suc (suc (n + n)) ≡⟨ cong (λ x → suc x) (p (n + n)) ⟩
    suc (n + n + 1) ≡⟨ p (n + n + 1) ⟩
    n + n + 1 + 1 ≡⟨ cong (λ x → x + 1 + 1) (p0 n) ⟩
    2 * n + 1 + 1 ≡⟨ refl ⟩
    2 * n + 2 ≡⟨ ? ⟩
    2 * (suc n)
  ∎
-}
{-
p2 : ∀ n → (2 ^ n) + (2 ^ n) ≡ 2 ^ (n + 1)
p2 zero    = refl
p2 (suc n) = 
  begin
    (2 ^ (suc n)) + (2 ^ (suc n)) ≡⟨ p0 ⟩
    2 * (2 ^ (suc n)) ≡⟨ refl ⟩
    2 ^ (suc (suc n)) ≡⟨ cong suc (λ x → 2 ^ x) (p (suc n)) ⟩
    2 ^ ((suc n) + 1)
  ∎
-}

{-
p1 : ∀ n  → n ^ 2 ≡ n * n
p1 zero = refl
p1 (suc n) =
  begin
    (suc n) ^ 2 ≡⟨ refl ⟩
    (suc n) * ((suc n) ^ 1) ≡⟨ refl ⟩
    (suc n) * ((suc n) * ((suc n) ^ zero)) ≡⟨ refl ⟩
    (suc n) * ((suc n) * 1) ≡⟨ refl ⟩
    (suc n) * (1 + n * 1) ≡⟨ refl ⟩
    (suc n) * (1 + 1 * n) ≡⟨ *-comm ⟩
    (suc n) * (1 + n + zero * n) ≡⟨ refl ⟩
    (suc n) * (1 + n + zero) ≡⟨ refl ⟩
    (suc n) * (suc n)
 ∎
-}