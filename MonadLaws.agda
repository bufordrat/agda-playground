module MonadLaws where

open import Agda.Primitive
open import Agda.Builtin.String
open import Function.Base
open import Agda.Builtin.Unit
open import Function.Construct.Composition
open import Agda.Builtin.Nat

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

  open Maybe

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

  open Maybe

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

module MonadsAreFunctors where

  record Monad : Set₁ where
    field

      Mon : Set₀ → Set₀

      _>>=_ : {A B : Set₀} →
              Mon A →
              (A → Mon B) →
              Mon B

      pure : {A : Set₀} → A → Mon A

      left_id : {A B : Set₀} →
                {x : A} →
                (k : A -> Mon B) →
                --------------------
                (pure x >>= k) ≡ k x

      right_id : {A : Set₀} →
                 (ma : Mon A) →
                 ---------------------
                 (pure ma >>= id) ≡ ma

      associativity : {A B C : Set₀} →
                      {f : A → Mon B} →
                      {g : B → Mon C} →
                      (ma : Mon A) →
                      ---------------------------
                      (
                      (ma >>= f) >>= g)
                      ≡ (ma >>= (λ a → f a >>= g)
                      )

  record Functor : Set₁ where
    field

      Func : Set₀ → Set₀

      map : {A B : Set₀} → (A → B) → Func A → Func B

      ident : {A B : Set₀} →
              (a : Func A) →
              ---------------
              map id a ≡ id a

      composition : {A B C : Set₀} →
                    {f : B → C} →
                    {g : A → B} →
                    (a : Func A) →
                    ------------------------------
                    map (f ∘ g) a ≡ map f (map g a)

    
  monads_are_functors : Monad → Functor
  monads_are_functors (record { Mon = m
                              ; _>>=_ = _>>=_
                              ; pure = pure
                              ; left_id = lid
                              ; right_id = rid
                              ; associativity = ass }) =
    record { Func = m
           ; map = λ f funky → funky >>= (λ simple -> pure (f simple))
           ; ident = {!!}
           ; composition = {!!} }
