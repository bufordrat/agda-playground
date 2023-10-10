module DependentProduct where

open import Data.Sum
open import Data.Bool
open import Data.Product

open import Data.Unit
open import Data.Nat

B : (x : ℕ) → Set
B 0 = ⊤
B _ = ℕ

partialSuc : (x : ℕ) → B x
partialSuc 0 = tt
partialSuc (suc n) = suc (suc n)

-- F : (x : Bool) → Set
-- F true = ⊤
-- F false = ℕ

-- productExample : Set
-- productExample = (x : Bool) → F x

BoolAndNat : Set
BoolAndNat = Bool × ℕ

both : BoolAndNat
both = false , 2

data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B

F : Bool → Set
F true = Bool
F false = ℕ

FancyBoolAndNat : Set
FancyBoolAndNat = (b : Bool) -> F b

fancyBoth : FancyBoolAndNat
fancyBoth true = false
fancyBoth false = 2

projections : BoolAndNat → (b : Bool) → F b
projections ( bool , _ ) true = bool
projections ( _ , nat ) false = nat

makeBothFancier : FancyBoolAndNat
makeBothFancier = projections both

-- PairUp : (x : Bool) →
--          (y : ℕ) →
--          (b : Bool) →
--          F b
-- PairUp x y true = x
-- PairUp x y false = y

-- BoolAndNat2 : (b : B

data Either (A B : Set) : Set where
  inj₁ : (x : A) → Either A B
  inj₂ : (y : B) → Either A B

FancyEither : (A B : Set) → Set
FancyEither A B = Σ Bool (λ { true → A ; false → B})

BoolOrNat : Set
BoolOrNat = Bool ⊎ ℕ

example1 : BoolOrNat
example1 = inj₁ true

example2 : BoolOrNat
example2 = inj₂ 12

FancyBoolOrNat : Set
FancyBoolOrNat = Σ Bool F

fancyExample1 : FancyBoolOrNat
fancyExample1 = true , true

fancyExample2 : FancyBoolOrNat
fancyExample2 = false , 12
