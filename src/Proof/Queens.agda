open import Abel.Category.Monad
open import Proof.MonadCount
open import Proof.MonadNonDet
open import Proof.MonadState

module Proof.Queens
  {M   : Set → Set}
  {Mm  : Monad'' M}
  {Mc  : MonadCount Mm}
  {Mnd : MonadNonDet Mm}
  (S   : Set)
  (Ms  : MonadState S Mm)
  where


open import Data.List
open import Data.Integer as ℤ
open import Data.Nat hiding (_≟_)
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Bool.Properties
open import Relation.Nullary.Decidable
open import Proof.Data.Tuple
open import Proof.Permutation

open Monad'' Mm
open MonadCount Mc
open MonadNonDet Mnd
open MonadState Ms

-- | Square type
Square : Set → Set
Square a = a x a

square : {A B : Set} → (A → B) → Square A → Square B
square f ⟨ a₁ , a₂ ⟩ = ⟨ f a₁ , f a₂ ⟩

guard : Bool → M ⊤
guard b = if b then skip else fail

assert : {A : Set} → (A → Bool) → M A → M A
assert p mx = mx >>= λ x → guard (p x) >> return x

-- | Boolean equality for Integers
_==_ : ℤ → ℤ → Bool
i₁ == i₂ = ⌊ i₁ ≟ i₂ ⌋

-- | Checks if a number is not on a list
_∉_ : ℤ → List ℤ → Bool
x ∉ []        = true
x ∉ (y ∷ ys) = if (x == y) then false else (x ∉ ys)

test : Square ℤ → Square (List ℤ) → Bool x Square (List ℤ)
test ⟨ c , r ⟩ ⟨ ups , downs ⟩ =
  ⟨ u ∉ ups ∧ d ∉ downs ,  ⟨ u ∷ ups , d ∷ downs ⟩ ⟩
  where
    u = r ℤ.- c
    d = r ℤ.+ c

start₁ : Square (List ℤ) → Bool x Square (List ℤ)
start₁ updowns = ⟨ true , updowns ⟩

step₁ : Square ℤ → Bool x Square (List ℤ) → Bool x Square (List ℤ)
step₁ cr ⟨ restOK , updowns ⟩ = ⟨ thisOK ∧ restOK , updowns' ⟩
  where
    aux      = test cr updowns
    thisOK   = fst aux
    updowns' = snd aux

-- | Function composition
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

safe₁ : Square (List ℤ) → List (Square ℤ) → Bool x Square (List ℤ)
safe₁ = foldr step₁ ∘ start₁

gen[ℤ] : ℕ → (List ℤ)
gen[ℤ] zero    = []
gen[ℤ] (suc n) = gen[ℤ] n ++ [ +(ℕ.suc n) ]

place : {A : Set} → ℕ → List A → List (ℤ x A)
place n = zipWith ⟨_,_⟩ (gen[ℤ] n)

empty : {A : Set} → Square (List A)
empty = ⟨ [] , [] ⟩

queens : ℕ → M (List ℤ)
queens n = perms Mnd n q >>=
  λ rs → guard (fst (safe₁ empty (place n rs))) >> return rs
  where
    q  = gen[ℤ] n


-- | Statefully implementation
start₂ : M Bool
start₂ = return true

step₂ : Square ℤ → M Bool → M Bool
step₂ cr k = k >>= (λ b' → get >>=
  (λ uds → let ⟨ b , uds' ⟩ = test cr uds
            in put uds' >> return (b ∧ b')))

safe₂ : List (Square ℤ) → M Bool
safe₂ = foldr step₂ start₂
