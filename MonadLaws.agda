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

    map : {A B : Set} → (A → B) → Maybe A → Maybe B
    map f ma = ma >>= λ a → pure (f a)

    module ItsAFunctor where

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

    module ItsAMonad where

        left_id : {A B : Set} →
                  {x : A} →
                  (k : A -> Maybe B) →
                  (pure x >>= k) ≡ k x
        left_id k = refl

        right_id : {A : Set} →
                   (ma : Maybe A) →
                   (pure ma >>= id) ≡ ma
        right_id (just x) = refl
        right_id nothing = refl

        associativity : {A B C : Set} →
                        {f : A → Maybe B} →
                        {g : B → Maybe C} →
                        (ma : Maybe A) →
                        ((ma >>= f) >>= g) ≡ (ma >>= (λ a → f a >>= g))
        associativity (just x) = refl
        associativity nothing = refl
