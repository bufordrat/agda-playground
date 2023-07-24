module MonadLaws where

open import Agda.Primitive
open import Agda.Builtin.String
open import Function.Base
open import Agda.Builtin.Unit
open import Function.Construct.Composition

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

module Maybe where

    data Maybe (A : Set) : Set where
     just : A → Maybe A
     nothing : Maybe A

    bind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
    bind (just x) k = k x
    bind nothing k = nothing

    infixl 1 _>>=_
    _>>=_ = bind

    pure : {A : Set} → A → Maybe A
    pure x = just x

    -- confirm that do notation works
    x : Maybe String
    x = do
      x <- just "hello"
      pure x

    map : {A B : Set} → (A → B) → Maybe A → Maybe B
    map f (just x) = just (f x)
    map f nothing = nothing

    funct_id : {A B : Set} →
               (a : Maybe A) →
               map id a ≡ id a
    funct_id (just j) = refl
    funct_id nothing = refl

    composition : {A B C : Set} →
                  {f : B → C} →
                  {g : A → B} →
                  (a : Maybe A) →
                  map (f ∘ g) a ≡ map f (map g a)
    composition (just x) = refl
    composition nothing = refl

    left_id : (A B : Set) →
              (x : A) →
              (k : A -> Maybe B) →
              (pure x >>= k) ≡ k x
    left_id A B x k = {!!}

