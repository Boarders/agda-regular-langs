{-# OPTIONS --guardedness #-}
module Languages (Σ : Set) where

open import Base
open import Data.List
open import Data.List.Properties
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (Σ to Pr₂)
open import Relation.Nullary
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Data.List.Relation.Unary.All
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Level
open import Function.Inverse hiding (_∘_)
open import Function using (_∘_)
open import Function.Equality using (Π)
open Π using (_⟨$⟩_)


variable
  ℓ : Level
  A B : Set ℓ

{-
====================
Specifying Languages
====================

Typically, we define a language as a subset of the
the collection of words Σ*.

We can identify such a subset S via its characteristic function:
s ⊆ Σ* ⇔ χₛ : Σ* → Bool
  where
    χₛ w | w ∈ S = True
    χₛ w | w ∉ S = False

Our starting point will be to enrich this situation from
a subset to the collection of _evidence_ that a word
is in a language. So we move from:

   Σ* → Bool ~> P : Σ* → Set

From the perspective of finite automata, we can think
of (P w) as something like the collection of all paths from a starting
state to an accepting state.

We can also fruitfully think of this as denoting proof-relevant languages or specifications.
-}

Lang : Set₁
Lang = Σ * → Set

{-
In this paradigm, here is how we can capture the regular languages:
-}

-- Interpretation: The language that never succeeds.
∅ : Lang
∅ = λ w → ⊥

-- Interpretation: The language that always succeeds.
𝒰 : Lang
𝒰 = λ w → ⊤

-- Interpretation: The language that parses precisely the empty string.
one : Lang
one = λ w → (w ≡ [])

infix 20 `_
infix 4 _∪_
infix 5 _∩_
infix 8 _∙_
infix 10 _☆

-- Interpretation: The language that parses a single character.
`_ : Σ → Lang
` c = λ w → w ≡ [ c ]

-- Interpretation: Takes a language P and set S and parses the same language with evidence indexed by S.
_∙_ : Set → Lang → Lang
S ∙ P = λ w → S × P w

-- Interpretation: Takes languages P and Q and succeeds if P succeeds or if Q succeeds.
_∪_ : Lang → Lang → Lang
P ∪ Q = λ w → P w ⊎ Q w

-- Interpretation: Takes languages P and Q and succeeds if P succeeds and if Q succeeds.
_∩_ : Lang → Lang → Lang
P ∩ Q = λ w → P w × Q w

-- Interpretation: Takes languages P and Q and succeeds if P followed by Q succeeds.
_*_ : Lang → Lang → Lang
P * Q = λ w → Σ[ (u , v) ∈ ((Σ *) × (Σ *)) ] ((w ≡ u ++ v) × P u × Q v)

-- Interpretation: Takes languages P and succeeds if P succeeds zero or more times.
data _☆ (P : Lang) : Lang where
  nil   : (P ☆) []
  push[] : ∀ {w} → P [] → (P ☆) w → (P ☆) w
  push∷  : ∀ {a u v} → P (a ∷ u) → (P ☆) v → (P ☆) (a ∷ (u ++ v))

{-
conceptually, this is the same as the following type:

_☆ : Lang → Lang
P ☆ = λ w → Σ[ ws ∈ List (Σ *) ] (w ≡ concat ws) × All P ws

However, this type of evidence is too painful to work with in agda.

-}

-- Go to Examples!

{-

====================
Brzozwski Derivative
====================

~ vague analogy ~
what is the pattern in the following sequence of numbers?

        2   5   10   17   26 ...
diff      3   5    7    9    ...
diff        2    2   2       ...

So the formula is quadratic and we can guess n² + 1

Formally, if we have f : ℕ → ℕ then we can take the
discrete derivative:

    (Δ f) n = f (n + 1) - f n

We can read this as the "jump" we can make at stage n to get to stage (n + 1)

Now, given a language L ⊆ Σ* and a word v ∈ Σ*, we can form the
brzozowski derivative 𝒟ᵥ : Lang → Lang

    𝒟ᵥ L = {w ∈ Σ* | vw ∈ L}

We can think of this as jumps from input v to get to an accepting state.

This allows us to split up the question of language recognition into:

 - nullability: When [] is in our language
 - derivative:  Use 𝒟ᵥ to advance the state we are in

-}

-- nullability
ν : (A * → B) → B
ν f = f []

-- total derivative
𝒟 : (L : A * → B) → (v : A *) → (A * → B)
𝒟 L v = λ w → L (v ++ w)

-- single derivative
δ : (A * → B) → A → (A * → B)
δ f v = 𝒟 f [ v ]

-- Property 1: We can recover the language from nullability and the
-- total derivative
ν∘𝒟 : ∀ {L : A * → B} → (ν ∘ 𝒟 L) ≡ L
ν∘𝒟 {L = L} = funExt (λ ws → cong L (++-identityʳ ws) )

-- Property 2: The derivative at [] acts as the identty:
𝒟[] : ∀ {L : A * → B} → 𝒟 L [] ≡ L
𝒟[] {L = L} = refl

-- Property 3: The derivative at u ++ v can be computed by composition of
-- the derivative at u and the derivative at v
𝒟++ : ∀ {L : A * → B}{u v : A *} → 𝒟 L (u ++ v) ≡ 𝒟 (𝒟 L u) v
𝒟++ {L = L} {u = u} {v = v} = funExt (λ w → cong L (++-assoc u v w))

-- Property 4: We can recover the total derivative from the single derivative
𝒟Lold∙ : ∀ (L : A * → B)(us : A *) → 𝒟 L us ≡ foldl δ L us
𝒟Lold∙ L [] = refl
𝒟Lold∙ L (u ∷ us) = 𝒟Lold∙ (δ L u) us

𝒟Lold : ∀ {L : A * → B} → 𝒟 L ≡ foldl δ L
𝒟Lold {L = L} = funExt (𝒟Lold∙ L)

{-

==============
Regular Lemmas
==============

This gives us a way of decomposing the subset of regular languages we saw earlier by recursively
analyzing the nullability and the derivatives of these languages.

-}

module RegularLemmas where

  variable
    P Q : Lang

{-
notation;

_≡_    : (Propostional) equality type
X ↔ Y : type of isomorphisms - constructed via maps f : X → Y, g : Y → X that are inverses to one another

-}

  ν∅ : ν ∅ ≡ ⊥
  ν∅ = refl

  ν𝒰 : ν 𝒰 ≡ ⊤
  ν𝒰 = refl

  ν∪ : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
  ν∪ = refl

  ν∩ : ν (P ∩ Q) ≡ (ν P × ν Q)
  ν∩ = refl

  νone : (ν one) ↔ ⊤
  νone = inverse (λ _ → tt) (λ _ → refl) (λ { refl → refl}) λ { tt → refl}

  ν* : (ν (P * Q)) ↔ (ν P × ν Q)
  ν* {P = P} {Q = Q} = inverse to from rInv lInv
    where
    to : (P * Q) [] → P [] × Q []
    to (([] , []) , refl , P[] , Q[]) = P[] , Q[]

    from : P [] × Q [] → (P * Q) []
    from (P[] , Q[]) = ([] , []) , refl , (P[] , Q[])

    rInv : (x : (P * Q) [] ) → from (to x) ≡ x
    rInv (([] , []) , refl , P[] , Q[]) = refl

    lInv : (x : (P [] × Q [])) → to (from x) ≡ x
    lInv (P[] , Q[]) = refl

  ν☆ : ν (P ☆) ↔ (ν P) *
  ν☆ {P = P} = inverse to from rInv lInv
    where
    to : (P ☆) [] → (P []) *
    to nil = []
    to (push[] p[] ps) = p[] ∷ to ps

    from : (P []) * →  (P ☆) []
    from [] = nil
    from (p[] ∷ p[]s) = push[] p[] (from p[]s)

    rInv : (x : (P ☆) [] ) → from (to x) ≡ x
    rInv nil = refl
    rInv (push[] p[] p[]s) rewrite rInv p[]s = refl

    lInv : (x : (P [])  *) → to (from x) ≡ x
    lInv [] = refl
    lInv (p[] ∷ p[]s) rewrite lInv p[]s = refl

  ν` : ∀ {c} → ν (` c) ↔ ⊥
  ν` {c = c} = inverse to from rInv lInv
    where
    to : (` c) [] → ⊥
    to ()

    from : ⊥ → (` c) []
    from ()

    rInv : (x : (` c) []) → from (to x) ≡ x
    rInv ()

    lInv : (x :  ⊥) → to (from x) ≡ x
    lInv ()

  δ∅ : {a : Σ} → δ ∅ a ≡ ∅
  δ∅ = refl

  δ𝒰 : {a : Σ} → δ 𝒰 a ≡ 𝒰
  δ𝒰 = refl

  δ∪ : {a : Σ} →  (δ (P ∪ Q) a) ≡ ((δ P a) ∪ (δ Q a))
  δ∪ = refl

  δ∩ : {a : Σ} →  (δ (P ∩ Q) a) ≡ ((δ P a) ∩ (δ Q a))
  δ∩ = refl

  δ∙ : {a : Σ} {s : Set} → δ (s ∙ P) a ≡ s ∙ δ P a
  δ∙ = refl

  δone : {a : Σ} → {w : Σ *} → δ one a w ↔ ∅ w
  δone {a = a} {w = w} = inverse to from rInv lInv
    where
    to : δ one a w → ⊥
    to ()
    
    from : ⊥ → δ one a w
    from ()

    rInv : (x : δ one a w) → from (to x) ≡ x
    rInv ()

    lInv : (x :  ⊥) → to (from x) ≡ x
    lInv ()

  δ* : {a : Σ} → {w : Σ *} → δ (P * Q) a w ↔ ((ν P) ∙ (δ Q a) ∪ (δ P a) * Q) w
  δ* {P = P} {Q = Q} {a = a} {w = w} = inverse to from rInv lInv
    where
    to : δ (P * Q) a w → ((ν P) ∙ (δ Q a) ∪ (δ P a) * Q) w
    to (([] , a ∷ v) , refl , P[] , Qav) = inj₁ (P[] , Qav)
    to ((x ∷ u , v) , refl , Pxu , Qv ) = inj₂ ((u , v) , (refl , (Pxu , Qv)))

    from :  ((ν P) ∙ (δ Q a) ∪ (δ P a) * Q) w → δ (P * Q) a w
    from (inj₁ (P[] , Qaw)) = ([] , a ∷ w) , refl , (P[] , Qaw)
    from (inj₂ ((u , v) , refl , Pau , Qv)) = ((a ∷ u) , v) , refl , (Pau , Qv)

    rInv : (x : δ (P * Q) a w) → from (to x) ≡ x
    rInv (([] , a ∷ v) , refl , P[] , Qav) = refl
    rInv ((x ∷ u , v) , refl , Pxu , Qv) = refl

    lInv : (x :  ((ν P) ∙ (δ Q a) ∪ (δ P a) * Q) w) → to (from x) ≡ x
    lInv (inj₁ (P[] , Qaw)) = refl
    lInv (inj₂ ((u , v) , refl , Pau , Qv)) = refl
  
  δ☆ : {a : Σ} → {w : Σ *} → δ (P ☆) a w ↔ ((List (ν P)) ∙ ((δ P a) * (P ☆))) w
  δ☆ {P = P} {a = a} {w = w} = inverse to from rInv lInv
    where
    to : δ (P ☆) a w → ((List (ν P)) ∙ ((δ P a) * (P ☆))) w
    to (push[] p[] ps) with to ps
    ... | p[]s , ps = p[] ∷ p[]s , ps
    to (push∷ {u = u} {v = v} pa ps) = [] , ((u , v) , refl , pa , ps)

    from :  ((List (ν P)) ∙ ((δ P a) * (P ☆))) w →  δ (P ☆) a w
    from ([] , (u , v) , refl , Pau , Qv) = push∷ Pau Qv
    from (p[] ∷ p[]s , (u , v) , eq , Pau , Qv) = push[] p[] (from ((p[]s , (u , v)  , eq , Pau , Qv)))

    rInv : (x : (P ☆) (a ∷ w)) → from (to x) ≡ x
    rInv (push[] p[] ps) rewrite rInv ps = refl
    rInv (push∷ pa ps) = refl

    lInv : (x :  ((List (ν P)) ∙ ((δ P a) * (P ☆))) w) → to (from x) ≡ x
    lInv ([] , (u , v) , refl , Pau , Qv) = refl
    lInv (p[] ∷ p[]s , (u , v) , eq , Pau , Qv) rewrite lInv (p[]s , (u , v) , eq , Pau , Qv) = refl

  δ` : ∀ {c a : Σ} → {w : Σ *} → δ (` c) a w ↔ ((a ≡ c) ∙ one) w
  δ` {c = c} {a = a} {w = w} = inverse to from rInv lInv
    where
    to : δ (` c) a w →  ((a ≡ c) ∙ one) w
    to refl = refl , refl
    
    from : ((a ≡ c) ∙ one) w →  δ (` c) a w
    from (refl , refl) = refl

    rInv : (x : δ (` c) a w) → from (to x) ≡ x
    rInv refl = refl

    lInv : (x : ((a ≡ c) ∙ one) w) → to (from x) ≡ x
    lInv (refl , refl) = refl

{-
============
Dedidability:
============

As we saw with the examples, for the regular languages we can expect to
be able to mechanically decide whether something is or is not in the language.


This is captured in type theory by the notion of Decidability:
-}

module Decidability where
  data Dec_ (X : Set) : Set where
    yes_ : X → Dec_ X
    no_  : ¬ X → Dec_ X

{-

Another way to view this: the decidable types are those for which the law of excluded middle holds.
We use the version of Dec from the agda standard library (which is defined slightly differently for efficiency reasons).

We will want to decide for any given input string if it is in our language so we will also need a pointwise
version of Dec:
-}

Dec∀ : {A : Set} → (P : A → Set) → Set
Dec∀ {A = A} P = ∀ (a : A) → Dec (P a)

{-
=================================
Compositionality of Decidability:
=================================

Decidable types are closed under various type formers and so will allow us to use the derivative to
inductively show a regular language is decidable:

-}

-- The empty type is decidable
⊥? : Dec ⊥
⊥? = no λ x → x

-- The unit type is decidable
⊤? : Dec ⊤
⊤? = yes tt


-- If A and B are decidable then so is their direct sum
_⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
no ¬a ⊎? no ¬b = no (⊎-elim ¬a  ¬b)
yes a ⊎? _ = yes (inj₁ a)
no ¬a ⊎? yes b = yes (inj₂ b)

-- If A and B are decidable then so is their direct product
_×?_ : Dec A → Dec B → Dec (A × B)
yes a ×? yes b = yes (a , b)
no ¬a ×? yes _ = no (¬a ∘ proj₁)
_ ×? no ¬b = no (¬b ∘ proj₂)

-- If A is decidable then so is List A
-- [in fact List A is always decidable as the proof makes clear]
_*? : Dec A  → Dec (List A)
_*? _ = yes []

-- If A is isomorphic to B then decidability of A implies decidability of B.
-- [We only actually need maps each way]
_↔?_ : B ↔ A → Dec A → Dec B
record { to = to ; from = from ; inverse-of = _ } ↔? dec with dec
... | yes a = yes (from ⟨$⟩ a)
... | no ¬a = no λ b → ¬a (to ⟨$⟩ b)

-- This also holds for pointwise decidable types
_↔∀?_ : ∀ {A : Set} → {P Q : A → Set} → (∀ {a : A} → Q a ↔ P a) → Dec∀ P → Dec∀ Q
_↔∀?_ iso dec-Q a = iso ↔? (dec-Q a)

{-
==========================
From Languages to Parsing:
==========================

Our plan will be to use these decidability lemmas to show that our parsing specifications are decidable.

We run into a problem: at present, we have a specification of the form:

  Lang = Σ* → Set

which we cannot inspect. In order to be able to recursively reason about the regular fragment and perform
 (co)induction to show decidability we need to either reify our regular language operations or reify ν and δ.
This is analagous to the situation for computing derivatives where we have two approaches:

  - symbolic: reify symbolically the functions under consideration.
  - automatic: reify the derivative and carry around the value (dual numbers)

-}

{-
========================
Symbolic Differentiation
========================
-}

{-
Note: We need our token type Σ to have decidable equality for both ways of showing the languages are
decidable;
-}
module Symbolic (_=Σ?_ : ∀ (x y : Σ) → Dec (x ≡ y)) where
{-
RegLang is an indexed datatype, we can think of the constructors as
what we would need to know to show a language is decidable:
-}
  data RegLang : Lang → Set₁ where
    ∅ᵣ : RegLang ∅
    𝒰ᵣ : RegLang 𝒰
    _⋃ᵣ_ : ∀ {P Q : Lang} → RegLang P → RegLang Q → RegLang (P ∪ Q)
    _⋂ᵣ_ : ∀ {P Q : Lang} → RegLang P → RegLang Q → RegLang (P ∩ Q)
    _∙ᵣ_ : ∀ {s : Set} {P : Lang} → Dec s → RegLang P → RegLang (s ∙ P)
    oneᵣ : RegLang one
    _*ᵣ_ : ∀ {P Q : Lang} → RegLang P → RegLang Q → RegLang (P * Q) 
    _☆ᵣ : ∀ {P : Lang} → RegLang P →  RegLang (P ☆)
    `ᵣ_  : (a : Σ) → RegLang (` a)
    _↔ᵣ_ : ∀ {P Q : Lang} → (∀ {w : Σ *} → Q w ↔ P w) → RegLang P → RegLang Q
  
  
  open RegularLemmas
  
  -- If we have a a regular language then it is decidable if the language
  -- is nullable.
  -- Notice: this follows exactly the recursive form of the ν Regular lemmas
  νᵣ : RegLang P → Dec (ν P)
  νᵣ ∅ᵣ = ⊥?
  νᵣ 𝒰ᵣ = ⊤?
  νᵣ (p ⋃ᵣ q) = νᵣ p ⊎? νᵣ q
  νᵣ (p ⋂ᵣ q) = νᵣ p ×? νᵣ q
  νᵣ (dec-a ∙ᵣ p) = dec-a ×? νᵣ p
  νᵣ oneᵣ = νone ↔? ⊤?
  νᵣ (p *ᵣ q) = ν* ↔? (νᵣ p ×? νᵣ q)
  νᵣ (p ☆ᵣ) = ν☆ ↔? ((νᵣ p) *?) 
  νᵣ (`ᵣ a) = ν` ↔? ⊥?
  νᵣ (iso ↔ᵣ p) = iso ↔? (νᵣ p)
  
  -- If a language is regular then the derivative is regular
  -- This again follows exactly the structure of the proofs of the δ Regular lemmas.
  δᵣ : RegLang P → (a : Σ) → RegLang (δ P a)
  δᵣ ∅ᵣ a = ∅ᵣ
  δᵣ 𝒰ᵣ a = 𝒰ᵣ
  δᵣ (p ⋃ᵣ q) a = δᵣ p a ⋃ᵣ δᵣ q a
  δᵣ (p ⋂ᵣ q) a = δᵣ p a ⋂ᵣ δᵣ q a
  δᵣ (x ∙ᵣ p) a = x ∙ᵣ (δᵣ p a)
  δᵣ oneᵣ a = δone ↔ᵣ ∅ᵣ
  δᵣ (p *ᵣ q) a = δ* ↔ᵣ ((νᵣ p ∙ᵣ δᵣ q a) ⋃ᵣ (δᵣ p a *ᵣ q) )
  δᵣ (p ☆ᵣ) a = δ☆ ↔ᵣ (((νᵣ p) *?) ∙ᵣ (δᵣ p a *ᵣ (p ☆ᵣ)))
  δᵣ (`ᵣ c) a = δ` ↔ᵣ ((a =Σ? c) ∙ᵣ oneᵣ )
  δᵣ (iso ↔ᵣ p) a = iso ↔ᵣ δᵣ p a
  
  -- Now we can show that any regular language is decidable:
  ⟦_⟧? : RegLang P → Dec∀ P
  ⟦ p ⟧? [] = νᵣ p
  ⟦ p ⟧? (a ∷ w) = ⟦ δᵣ p a ⟧? w


module Automatic (_=Σ?_ : ∀ (x y : Σ) → Dec (x ≡ y)) where
  open RegularLemmas

  -- Here, instead of an inductive type, we have a coinducitve
  -- type describing a coinductive trie type structure:
  record Machine (P : Lang) : Set₁ where
    coinductive
    field
      νₘ : Dec (ν P)
      δₘ : (a : Σ) → Machine (δ P a)

  open Machine
  
  -- We can show that any language indexed by a Machine
  -- is decidable:
  ⟦_⟧? : Machine P → Dec∀ P
  ⟦ p ⟧? [] = νₘ p
  ⟦ p ⟧? (a ∷ w) = ⟦ δₘ p a ⟧? w
  
  -- Now we can show the coinductive trie of each of the regular languages,
  -- hence showing they are decidable:
  --
  -- Note: These again follow the inductive structure of the regular lemmas:
  ∅ₘ : Machine ∅
  νₘ ∅ₘ = ⊥?
  δₘ ∅ₘ a = ∅ₘ

  𝒰ₘ : Machine 𝒰
  νₘ 𝒰ₘ = ⊤?
  δₘ 𝒰ₘ a = 𝒰ₘ

  _↔ₘ_ :  (∀ {w : Σ *} → Q w ↔ P w) → Machine P → Machine Q
  νₘ (iso ↔ₘ p) = iso ↔? νₘ p 
  δₘ (iso ↔ₘ p) a = iso ↔ₘ (δₘ p a)

  _⋃ₘ_ : Machine P → Machine Q → Machine (P ∪ Q)
  νₘ (p ⋃ₘ q) = νₘ p ⊎? νₘ q
  δₘ (p ⋃ₘ q) a = δₘ p a ⋃ₘ δₘ q a

  _⋂ₘ_ : Machine P → Machine Q → Machine (P ∪ Q)
  νₘ (p ⋂ₘ q) = νₘ p ⊎? νₘ q
  δₘ (p ⋂ₘ q) a = δₘ p a ⋂ₘ δₘ q a

  _∙ₘ_ : ∀ {s : Set} → Dec s → Machine P → Machine (s ∙ P)
  νₘ (D ∙ₘ p) = D ×? νₘ p
  δₘ (D ∙ₘ p) a = D ∙ₘ δₘ p a

  oneₘ : Machine one
  νₘ oneₘ = νone ↔? ⊤?
  δₘ oneₘ a = δone ↔ₘ ∅ₘ

  {-# TERMINATING #-}
  -- Due to limitations in Agda's coinduction it cannot see that the following coinductive definitions
  -- are terminating.
  --
  -- The paper uses sized-types to get around this issue.
  _*ₘ_ : Machine P → Machine Q → Machine (P * Q)
  νₘ (p *ₘ q) = ν* ↔? ((νₘ p) ×? (νₘ q))
  δₘ (p *ₘ q) a = δ* ↔ₘ ((νₘ p ∙ₘ δₘ q a) ⋃ₘ (δₘ p a *ₘ q))

  {-# TERMINATING #-}
  _☆ₘ : Machine P → Machine (P ☆)
  νₘ (p ☆ₘ) = ν☆ ↔? ((νₘ p) *?)
  δₘ (p ☆ₘ) a = δ☆ ↔ₘ (((νₘ p) *?) ∙ₘ ((δₘ p a) *ₘ (p ☆ₘ)))

  
  `ₘ : (c : Σ) → Machine (` c)
  νₘ (`ₘ c) = ν` ↔? ⊥?
  δₘ (`ₘ c) a = δ` ↔ₘ ((a =Σ? c) ∙ₘ oneₘ)
