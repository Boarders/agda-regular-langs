{-# OPTIONS --guardedness #-}
module Examples where

open import Data.List
open import Data.Char
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Base
open import Languages (Char)

a∪b : Lang
a∪b = (` 'a') ∪ (` 'b')

a*b : Lang
a*b = (` 'a') * (` 'b')

_ : a∪b [ 'b' ]
_ = inj₂ refl -- inj₂ refl

_ : a*b ( 'a' ∷ 'b' ∷ [] )
_ =  u,v , refl , refl , refl
  where
    u,v : (Char *) × (Char *)
    u,v =  [ 'a' ] ,  [ 'b' ]
