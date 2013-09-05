module Monads.Data.Tuple where

data _x_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A x B

fst : {A B : Set} -> A x B -> A
fst ⟨ x , y ⟩ = x

snd : {A B : Set} -> A x B -> B
snd ⟨ x , y ⟩ = y