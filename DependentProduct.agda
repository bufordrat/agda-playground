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

F : (x : Bool) → Set
F true = ⊤
F false = ℕ

productExample : Set
productExample = (x : Bool) → F x

BoolAndNat : Set
BoolAndNat = Bool × ℕ

data Pair (A : Set) (B : Set) : Set where
  _,_ : A → B → Pair A B

FancyPair : (A : Set) → (B : Set) → Bool → Set
FancyPair A B true = A
FancyPair A B false = B

data Either (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → Either A B
  inj₂ : (y : B) → Either A B

FancyEither : (A : Set) → (B : Set) → Set
FancyEither A B = Σ Bool (λ { true → A ; false → B})

