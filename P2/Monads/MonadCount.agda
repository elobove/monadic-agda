module Monads.MonadCount where

open import Abel.Category.Monad
open import Abel.Category.Applicative
open import Abel.Category.Functor

open import Data.Nat
open import Data.Maybe

------------------------------------------------------------------
-- Unit type

data ⊤ : Set where
  tt : ⊤

------------------------------------------------------------------
-- MonadCount

record MonadCount (M : Set → Set) {applicative : Applicative M}
                  {monad : Monad M {applicative}} : Set₁ where
  constructor
    mkMonadCount

  field
    tick : M ⊤

skip : {M : Monad} → M ⊤
skip = return tt

hanoi : {M : MonadCount} → ℕ → M ⊤
hanoi zero    = skip
hanoi (suc n) = hanoi n >> tick >> hanoi n


rep : {A : Set} {M : Set → Set} {monad : Monad M} → ℕ → M A → M A
rep zero    mx = skip
rep (suc n) mx = mx >> rep n mx

p1 : {mx : Monad T} → rep 1 mx ≡ mx
p1 refl = refl

p2 : {mx : Monad T}(m n : ℕ) → rep (m + n) mx ≡ (rep m mx >> rep n mx)
p2 refl = refl

prueba : ∀{n} → hanoi n ≡ (rep ((2^n)-1) tick)
prueba zero    = hanoi zero
prueba (suc n) =
  hanoi n >> tick >> hanoi n ≡⟨ hanoi (suc n) ⟩
  rep ((2^n)-1) tick >> tick >> rep ((2^n)-1) tick ≡⟨ p1⟩
  rep ((2^n)-1) tick >> rep 1 tick >> rep ((2^n)-1) tick ≡⟨ p2 rep ((2^n)-1) 1⟩
  rep ((2^n)-1+1) tick >> rep ((2^n)-1) tick ≡⟨ p2 ((2^n)-1+1) 1 ⟩
  rep ((2^n)-1+1+(2^n)-1) tick ≡⟨ ⟩
  rep ((2^n)+(2^n)-1+1-1) tick ≡⟨ ⟩
  rep ((2^(n+1))-1+1-1) tick ≡⟨ ⟩
  rep ((2^(n+1))-1) tick ◼