open import Abel.Category.Monad
open import Proof.MonadCount
open import Proof.MonadNonDet
open import Proof.MonadState

open import Data.List
open import Data.Integer as ℤ
open import Proof.Data.Tuple

module Proof.StateQueens
  {M   : Set → Set}
  {Mm  : Monad'' M}
  {Mc  : MonadCount Mm}
  {Mnd : MonadNonDet Mm}
  (Ms  : MonadState (List ℤ x List ℤ) Mm)
  where

open import Proof.Queens {M} {Mm} {Mc} {Mnd} (List ℤ x List ℤ) Ms
open import Data.Bool

open Monad'' Mm
open MonadCount Mc
open MonadNonDet Mnd
open MonadState Ms

-- | Statefully implementation
start₂ : M Bool
start₂ = return true

step₂ : Square ℤ → M Bool → M Bool
step₂ cr k = k >>= (λ b' → get >>=
  (λ uds → let aux = test cr uds
            in put (snd aux) >> return (fst aux ∧ b')))

safe₂ : List (Square ℤ) → M Bool
safe₂ = foldr step₂ start₂
