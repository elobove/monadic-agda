------------------------------------------------------------------------------
-- | Monad: Kleisli triple or monad in extension form
-- | Taked from: Abel ( https://github.com/jpvillaisaza/abel )
------------------------------------------------------------------------------

module Proof.Monad where

open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit

------------------------------------------------------------------------------
-- Monad

record Monad (M : Set → Set) : Set₁ where

  constructor mkMonad

  field

    return : {A : Set} → A → M A

    bind   : {A B : Set} → (A → M B) → M A → M B

    associativity : {A B C : Set} {f : A → M B} {g : B → M C} (mx : M A) →
                    bind g (bind f mx) ≡ bind (bind g ∘ f) mx

    unity-left    : {A B : Set} {f : A → M B} (x : A) →
                    bind f (return x) ≡ f x

    unity-right   : {A : Set} (mx : M A) → bind return mx ≡ mx

  infixr 1 _=<<_

  _=<<_ : {A B : Set} → (A → M B) → M A → M B
  _=<<_ = bind

  infixl 1 _>>=_ _>>_

  _>>=_ : {A B : Set} → M A → (A → M B) → M B
  mx >>= f = bind f mx

  _>>_ : {A B : Set} → M A → M B → M B
  mx >> my = mx >>= λ _ → my

  fmap : {A B : Set} → (A → B) → M A → M B
  fmap f = bind (return ∘ f)

  join : ∀ {A} → M (M A) → M A
  join = bind id

  skip : M ⊤
  skip = return tt
