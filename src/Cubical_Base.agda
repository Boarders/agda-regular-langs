{-# OPTIONS --cubical #-}

module Base where

open import Cubical.Data.List
open import Cubical.Foundations.Everything hiding (Σ; _∙_)
open import Data.Product
open import Cubical.Data.Empty renaming (rec to ⊥-ind)

_* : Set → Set
_* = List

concat : ∀ {A : Set} → List (List A) → List A
concat = foldr _++_ []

isSetList : ∀ {A : Set} → isSet A → isSet (List A)
isSetList = isOfHLevelList 0

++-=-[] : {A : Set} (u v : List A) → [] ≡ u ++ v → (u ≡ [] × v ≡ [])
++-=-[] [] [] _ = refl , refl
++-=-[] [] (x ∷ v) eq = ⊥-ind (¬nil≡cons eq)
++-=-[] (x ∷ u) v eq = ⊥-ind (¬nil≡cons eq)
