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
             (ma >>= pure) ≡ ma
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

  module Bind where

    record Monad : Set₁ where
      field

        Mon : Set₀ → Set₀

        _>>=_ : {A B : Set₀} →
                Mon A →
                (A → Mon B) →
                Mon B

        pure : {A : Set₀} → A → Mon A

        left_id : {A B : Set₀} →
                  (x : A) →
                  (k : A -> Mon B) →
                  --------------------
                  (pure x >>= k) ≡ k x

        right_id : {A : Set₀} →
                   (ma : Mon A) →
                   ---------------------
                   ma >>= pure ≡ ma

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
                    (f : B → C) →
                    (g : A → B) →
                    (a : Func A) →
                    ------------------------------
                    map (f ∘ g) a ≡ map f (map g a)

    
  m2f : Bind.Monad → Functor
  m2f (record { Mon = M
              ; _>>=_ = _>>=_
              ; pure = pure
              ; left_id = left_id
              ; right_id = right_id
              ; associativity = associativity }) =
    record { Func = M
           ; map = map
           ; ident = right_id
           ; composition = composition }
      where
        map : {A B : Set} → (A → B) → M A → M B
        map f func = func >>= λ simple → pure (f simple)

        identity : {A B : Set} →
                   (ma : M A) →
                   map id ma ≡ id ma
        identity ma =
          begin
            map id ma
          ≡⟨ refl ⟩                         -- definition of map
            ma >>= (λ a → pure (id a))
          ≡⟨ refl ⟩                         -- definition of _∘_
            ma >>= (pure ∘ id)
          ≡⟨ refl ⟩                         -- definition of id
            ma >>= pure
          ≡⟨ right_id ma ⟩
            ma
          ≡⟨ refl ⟩                         -- definition of id
            id ma
          ∎

        composition : {A B C : Set} → 
                      (f : B → C) →
                      (g : A → B) →
                      (ma : M A) →
                      map (f ∘ g) ma ≡ map f (map g ma)
        composition {A} {B} f g ma =
          begin
            map (f ∘ g) ma
          ≡⟨ refl ⟩
            ma >>= (λ a → pure ((f ∘ g) a))
          ≡⟨ refl ⟩
            ma >>= (λ a → pure (f (g a)))
          ≡⟨ {!!} ⟩
            ma >>= (λ a → pure (g a) >>= (pure ∘ f))
          ≡⟨ refl ⟩
            ma >>= (λ a → pure (g a) >>= (pure ∘ f))
          ≡⟨ refl ⟩
            ma >>= (λ a → (pure ∘ g) a >>= (pure ∘ f))
          ≡⟨ sym (associativity ma) ⟩
            (ma >>= (pure ∘ g)) >>= (pure ∘ f)
          ≡⟨ refl ⟩
            (ma >>= (λ b → pure (g b))) >>= (pure ∘ f)
          ≡⟨ refl ⟩
            (ma >>= (λ b → pure (g b))) >>= (λ c → pure (f c))
          ≡⟨ refl ⟩
            map f (map g ma)
          ∎
            where
              lhs = ma >>= λ a → (pure ∘ f) (g a)
              rhs = ma >>= λ a → pure (g a) >>= (pure ∘ f)
              lemma : (x : A) →
                      (k : A → M B) → 
                      (pure x >>= k ≡ k x) →
                      lhs ≡ rhs
              lemma x k lid =
                begin
                  ma >>= (λ a → pure (f (g a)))
                ≡⟨ {!!} ⟩
                  ma >>= (λ a → pure (g a) >>= (λ x → pure (f x)))
                ∎
