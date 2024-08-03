module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Relation.Unary

postulate □ : Set → Set
postulate unemployment_goes_up : Set
postulate mw_raise : Set

don't_raise_mw : □ (¬ mw_raise)
don't_raise_mw =
  don't_raise_unemployment mw_raises_unemployment
    where
      don't_raise_unemployment : {X : Set} →
                                 (X → unemployment_goes_up) →
                                 □ (¬ X)
      don't_raise_unemployment = {!!}

      mw_raises_unemployment : mw_raise → unemployment_goes_up
      mw_raises_unemployment = {!!}

postulate R : Set
postulate Un : Set

N : □ (¬ R)
N =
  Un_is_bad R→Un
    where
      Un_is_bad : {X : Set} → (X → Un) → □ (¬ X)
      Un_is_bad = {!!}

      R→Un : R → Un
      R→Un = {!!}

