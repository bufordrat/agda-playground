open import Agda.Primitive
open import Agda.Builtin.String
open import Function.Base
open import Agda.Builtin.Unit

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

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

funct_id : (A B : Set) →
           (a : Maybe A) →
           map id a ≡ id a
funct_id A B (just j) = refl
funct_id A B nothing = refl

composition : (A B C : Set) →
              (a : Maybe A) →
              (f : B → C) →
              (g : A → B) →
              ⊤
              -- map f (g a) ≡ map f (map g a)
composition A B C a f g = {!!}
