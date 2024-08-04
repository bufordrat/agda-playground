module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Function

-- to avoid having to define □
postulate □ : Set → Set

module Axioms where

  -- R: "minimum wage is raised"
  postulate R : Set
  -- L: "mass layoffs happen"
  postulate L : Set
  -- M: "unemployment goes up"
  postulate M : Set

module InferenceRules where
  open Axioms

  -- R→L: "if the minimum wage is raised, mass layoffs happen"
  postulate R→L : R → L
  -- L→M: "if mass layoffs happen, unemployment goes up
  postulate L→M : L → M
  -- □¬M: "if X raises unemployment, don't do X"
  postulate □¬M : {X : Set} → (X → M) → □ (¬ X)

module Argument where
  open Axioms
  open InferenceRules

  -- N: "don't raise the minimum wage"
  N : □ (¬ R)
  N = □¬M (L→M ∘ R→L)



-- -- atomic propositions
-- postulate mw_raise : Set
-- postulate unemployment_goes_up : Set
-- postulate mass_layoffs : Set

-- -- axioms
-- postulate mw_layoffs : mw_raise → mass_layoffs
-- postulate unem_layoffs : mass_layoffs → unemployment_goes_up
-- postulate don't_raise_unemployment : {X : Set} →
--                                      (X → unemployment_goes_up) →
--                                      □ (¬ X)

-- don't_raise_mw : □ (¬ mw_raise)
-- don't_raise_mw =
--   don't_raise_unemployment mw_raises_unemployment
--     where
--       mw_raises_unemployment : mw_raise → unemployment_goes_up
--       mw_raises_unemployment = unem_layoffs ∘ mw_layoffs

-- don't_raise_mw' : □ (¬ mw_raise)
-- don't_raise_mw' =
--   don't_raise_unemployment (unem_layoffs ∘ mw_layoffs)

