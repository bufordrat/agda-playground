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

data Either (A : Set₀) (B : Set₀) : Set₀ where
  inj₁ : (x : A) → Either A B
  inj₂ : (y : B) → Either A B

FancyEither : (A : Set₀) → (B : Set₀) → Set₀
FancyEither A B = Σ Bool (λ { true → A ; false → B})
