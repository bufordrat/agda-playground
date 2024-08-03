module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Relation.Unary
open import Function

postulate □ : Set → Set

-- atomic propositions
postulate mw_raise : Set
postulate unemployment_goes_up : Set
postulate mass_layoffs : Set

postulate mw_layoffs : mw_raise → mass_layoffs
postulate unem_layoffs : mass_layoffs → unemployment_goes_up
postulate don't_raise_unemployment : {X : Set} →
                                     (X → unemployment_goes_up) →
                                     □ (¬ X)

don't_raise_mw : □ (¬ mw_raise)
don't_raise_mw =
  don't_raise_unemployment mw_raises_unemployment
    where
      mw_raises_unemployment : mw_raise → unemployment_goes_up
      mw_raises_unemployment = unem_layoffs ∘ mw_layoffs

don't_raise_mw' : □ (¬ mw_raise)
don't_raise_mw' =
  don't_raise_unemployment (unem_layoffs ∘ mw_layoffs)

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

