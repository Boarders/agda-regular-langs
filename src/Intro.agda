{-# OPTIONS --cubical #-}

module Intro where

--open import Cubical.Core.Primitives
open import Level

{-

Martin-Löf's dependent type theory allows one to reason about mathematical equality. One of
the ways this is acheived is via the identity type. In Agda, this is traditionally defined
as an indexed data type as follows:

-}
module MLEquality where
  infixr 30 _∙_
  infix 4 _≡_
  variable
    X : Set

  data _≡_ (x : X) : X → Set where
    refl : x ≡ x

  variable
    x y z w : X
    p : x ≡ y
    q : y ≡ z
    r : z ≡ w

{-

One curious feature, discovered by a number of researchers (Hofmann, Streicher, Awodey, Voevodske etc.) is
is that this type embodies an infinity groupoid.

A (plain) groupoid is a category for which all morphisms are invertible. One can thus think of a groupoid
as a kind of "typed group". Another, perhaps more helpful, intuition is provided by the _fundamental groupoid_
of a space X - $\Pi(X)$. This has:
$$
\def\Ob{\mathsf{Ob}}
\def\Mor{\mathsf{Hom}}
\def\x{\mathrm{x}}
\def\y{\mathrm{y}}
\Ob(\Pi(X)) = \{\mathrm{points of X}\}
\Mor(x, y) = \{ \mathrm{paths from x to y} \}/\
$$

 This structure is exhibited in some form by the identity type which has an
identity and composition law
-}
  id : x ≡ x
  id = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ refl = refl

{-

Typically for a groupoid $\mathcal{G}$ we would also have laws dictating that the identity acts trivially on the left and
right and that composition is associative:

$$
\def\id{\mathrm{id}}
\def\mor#1{\mathrm{#1}}
\id \circ \mor{f} = \mor{f}
\mor{f} \circ \id
(\mor{f} \circ \mor{g}) \circ \mor{h} =  \mor{f} \circ (\mor{g} \circ \mor{h})
$$

We can define these for our identity type, but we note that they do not hold _definitionally_:
-}

  id-l : ∀ (p : x ≡ y) → (id  ∙ p ≡ p)
--  id-l p = refl: If we try to just give refl we get back: refl ∙ p != p of type x ≡ 
  id-l refl = refl

  id-r : ∀ (p : x ≡ y) → (p ∙ id ≡ p)
  id-r refl = refl

  assoc : ∀ (p : x ≡ y) (q : y ≡ z) (w : z ≡ w) → ((p ∙ q) ∙ w ≡ p ∙ (q ∙ w))
  assoc refl refl refl = refl

{-

Since these laws don't hold definitionally we might then expect higher laws hold, for example that
the two different ways to traverse the following diagram are equal:

$$
PENTAGON LAW
$$
-}
 
open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1
open import Data.Nat
open import Cubical.Foundations.Equiv
open import Data.Unit
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation

lem : (f g : ℕ → S¹) → (n : ℕ) → f n ≡ g n
lem f g n  with f n | g n 
... | base | base = {!!}
... | base | loop i = {!!}
... | loop i | base = {!!}
... | loop i | loop i₁ = {!!}

f : Iso (ℕ → S¹) ⊤
f = 
    iso to from to∘from from∘to
  where
  to : (ℕ → S¹) → ⊤
  to _ = tt

  from : ⊤ → (ℕ → S¹)
  from _ = λ _ → base

  to∘from : section to from
  to∘from tt = refl


  from∘to : retract to from
  from∘to f = funExt λ n → {!!}
