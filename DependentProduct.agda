module DependentProduct where

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

data Either (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → Either A B
  inj₂ : (y : B) → Either A B

FancyEither : (A : Set) → (B : Set) → Set
FancyEither A B = Σ Bool (λ { true → A ; false → B})
