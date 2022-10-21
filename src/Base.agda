module Base where

open import Data.List
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Level

_* : Set → Set
_* = List

++-=-[] : {A : Set} (u v : List A) → [] ≡ u ++ v → (u ≡ [] × v ≡ [])
++-=-[] [] [] _ = refl , refl
++-=-[] [] (x ∷ v) ()
++-=-[] (x ∷ u) v ()

-- concat-[] : {A : Set} (wss : List (List A)) → concat wss ≡ [] → wss ≡ [] ∷ []
-- concat-[] wss = {!!}

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : A → Set ℓ'

postulate
  funExt : ∀ {f g : (a : A) → B a} → (∀ (a : A) → f a ≡ g a) → f ≡ g
