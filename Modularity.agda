module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Relation.Unary

-- let's assume box as a primitive
□ : Set → Set
□ = {!!}

mw_raise : Set
mw_raise = {!!}

don't_raise_mw : □ (¬ mw_raise)
don't_raise_mw =
  don't_raise_unemployment mw_raises_unemployment
    where
      unemployment_goes_up : Set
      unemployment_goes_up = {!!}

      don't_raise_unemployment : {X : Set} →
                                 (X → unemployment_goes_up) →
                                 □ (¬ X)
      don't_raise_unemployment = {!!}

      mw_raises_unemployment : mw_raise → unemployment_goes_up
      mw_raises_unemployment = {!!}

R : Set
R = {!!}

Un : Set
Un = {!!}

N : □ (¬ R)
N =
  □¬R R→Un
    where
      □¬R : {X : Set} → (X → Un) → □ (¬ X)
      □¬R = {!!}

      R→Un : R → Un
      R→Un = {!!}

