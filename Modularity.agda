module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Function

-- shortcut to avoid having to define □
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

module RefactoredPremise where
  open Axioms
  open InferenceRules

  -- N: "don't raise the minimum wage"
  N : □ (¬ R)
  N = □¬M R→M
    where
      -- R→M: "if the minimum wage is raised,
      --       unemployment goes up"
      R→M : R → M
      R→M = L→M ∘ R→L
