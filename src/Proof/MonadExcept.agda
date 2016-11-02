------------------------------------------------------------------------------
-- | MonadExcept:
------------------------------------------------------------------------------

module Proof.MonadExcept where

open import Abel.Category.Monad
open import Proof.MonadNonDet
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------
-- MonadExcept

record MonadExcept {M : Set → Set} {Mnd : Monad'' M}
  (monad : MonadNonDet Mnd) : Set₁ where

  constructor
    mkMonadExcept

  open Monad'' Mnd
  open MonadNonDet monad

  field
    catch        : {A : Set} → M A → M A → M A

    catch-fail₁  : {A : Set} (h : M A) → catch fail h ≡ h

    catch-fail₂  : {A : Set} (m : M A) → catch m fail ≡ m

    catch-catch  : {A : Set} (m h h' : M A) →
      catch m (catch h h') ≡ catch (catch m h) h'

    catch-return : {A : Set} (x : A) (h : M A) → catch (return x) h ≡ return x
