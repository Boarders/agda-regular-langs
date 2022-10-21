{-# OPTIONS --cubical #-}
-- {-# OPTIONS --type-in-type #-}

open import Cubical.Foundations.Everything hiding (Σ; _∙_)

module Languages (Σ : Set) (Σ-Set : isSet Σ) where

open import Base
open import Cubical.Data.List
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Data.Product using (_×_)

open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Data.List.Relation.Unary.All
open import Cubical.Data.Empty renaming (rec to ⊥-ind)


variable
  ℓ : Level
  A B : Set ℓ

{-

Typically, we define a language as a subset of the
the collection of words Σ*.

We can identify such a subset S as a function:
s ⊆ Σ* ⇔ χₛ : Σ* → Bool
  where
    χₛ w | w ∈ S = True
    χₛ w | w ∉ S = False

Our starting point will be to enlarge this from
a subset to the collection of _evidence_ that a word
is in a language. So we move from:
   Σ* → Bool ~> P : Σ* → Set

From the perspective of finite automatas, we can think
of (P w) as the collection of all paths from a starting
state to an accepting state.

We can also think of this as denoting proof-relevant languages or specifications.
-}

Lang : Set₁
Lang = Σ * → Set

{-
In this paradigm, here is how we can capture the regular languages:
-}

∅ : Lang
∅ = λ w → ⊥

𝒰 : Lang
𝒰 = λ w → ⊤

one : Lang
one = λ w → (w ≡ [])

-- infix 20 `_
-- infix 4 _∪_
-- infix 5 _∩_
-- infix 10 _☆

`_ : Σ → Lang
` c = λ w → w ≡ [ c ]

_∙_ : Set → Lang → Lang
S ∙ P = λ w → S × P w

_∪_ : Lang → Lang → Lang
P ∪ Q = λ w → P w ⊎ Q w

_∩_ : Lang → Lang → Lang
P ∩ Q = λ w → P w × Q w

_*_ : Lang → Lang → Lang
P * Q = λ w → Σ[ (u , v) ∈ (Σ *) × (Σ *) ] (w ≡ u ++ v) × P u × Q v

_☆ : Lang → Lang
P ☆ = λ w → Σ[ ws ∈ List (Σ *) ] (w ≡ concat ws) × All P ws

-- Go to Examples!

{-

brzozwski derivative

~ vague analogy ~
what is the pattern?

        2   5   10   17   26 ...
diff      3   5    7    9    ...
diff        2    2   2       ...

So the formula is quadratic and we can guess n² + 1

formally if we have f : ℕ → ℕ then we can take the
discrete derivative:

    (Δ f) n = f (n + 1) - f n

We can read this as the "jump" we can make at stage n.

Now, given a language L ⊆ Σ* and a word v ∈ Σ*, we can form the
brzozowski derivative δᵥ : Lang → Lang

    δᵥ L = {w ∈ Σ* | vw ∈ L}

-}


-- nullability
ν : (A * → B) → B
ν f = f []

-- total derivative
𝒟 : (A * → B) → A * → (A * → B)
𝒟 f v = λ w → f ( v ++ w)

-- single derivative
δ : (A * → B) → A → (A * → B)
δ f v = 𝒟 f [ v ]

-- Property 1: We can recover the language from nullability and the
-- derivative


ν∘𝒟 : ∀ {f : A * → B} → ν ∘ 𝒟 f ≡ f
ν∘𝒟 {f = f} = funExt (λ ws → cong f (++-unit-r ws))

𝒟[] : ∀ {f : A * → B} → 𝒟 f [] ≡ f
𝒟[] {f = f} = refl

𝒟++ : ∀ {f : A * → B}{u v : A *} → 𝒟 f (u ++ v) ≡ 𝒟 (𝒟 f u) v
𝒟++ {f = f} {u = u} {v = v} = funExt (λ w → cong f (++-assoc u v w))

𝒟fold∙ : ∀ (f : A * → B)(us : A *) → 𝒟 f us ≡ foldl δ f us
𝒟fold∙ f [] = refl
𝒟fold∙ f (u ∷ us) = 𝒟fold∙ (δ f u) us

𝒟fold : ∀ {f : A * → B} → 𝒟 f ≡ foldl δ f
𝒟fold {f = f} = funExt (𝒟fold∙ f)

module RegularLemmas where

  variable
    P Q : Lang

  ν∅ : ν ∅ ≡ ⊥
  ν∅ = refl

  ν𝒰 : ν 𝒰 ≡ ⊤
  ν𝒰 = refl

  ν∪ : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
  ν∪ = refl

  ν∩ : ν (P ∩ Q) ≡ (ν P × ν Q)
  ν∩ = refl

  νone : Iso (ν one) ⊤
  νone = iso (λ _ → tt) (λ _ → refl) (λ { tt → refl}) λ path → isSetList Σ-Set [] [] refl path

  
  v* : (ν (P * Q)) ≃ (ν P × ν Q)
  v* {P = P} {Q = Q} = to , record { equiv-proof = equiv }
    where
    to : (P * Q) [] → P [] × Q []
    to ((u , v) , (pf , P[u] , Q[v])) with ++-=-[] u v pf 
    ... | (u≡[] , v≡[]) = subst P u≡[] P[u] , subst Q v≡[] Q[v]

    equiv : (y : ν P × ν Q) → isContr (fiber to y)
    equiv (P[] , Q[]) = ((([] , {!!}) , {!!}) , {!!}) , {!!}
{-
  v* : Iso (ν (P * Q)) (ν P × ν Q)
  v* {P = P} {Q = Q} = iso to from rInv lInv
    where
    to : (P * Q) [] → P [] × Q []
    to ((u , v) , (pf , P[u] , Q[v])) with ++-=-[] u v pf 
    ... | (u≡[] , v≡[]) = subst P u≡[] P[u] , subst Q v≡[] Q[v]

    from : P [] × Q [] → (P * Q) []
    from (P[] , Q[]) = ([] , []) , (refl , (P[] , Q[]))

    rInv : section to from
    rInv (P[] , Q[]) = λ i → (transportRefl P[] i) , (transportRefl Q[] i)

    lInv : retract to from
    lInv (([] , []) , pf , P[u] , Q[v]) = 
       λ i →  ([] , []) , ((isSetList Σ-Set [] [] refl pf i) , (transportRefl P[u] i , transportRefl Q[v] i))
    lInv (([] , x ∷ v) , pf , P[u] , Q[v]) = ⊥-ind (¬nil≡cons pf)
    lInv ((x ∷ u , v) , pf , P[u] , Q[v]) = ⊥-ind (¬nil≡cons pf)
-}
  -- ν☆ : Iso (ν (P ☆)) ((ν P) *)
  -- ν 
  
  

{-

dedidability

-}

