module Modularity where

open import Data.Empty
open import Relation.Nullary
open import Function

-- shortcut to avoid having to define □
postulate □ : Set → Set

module Axioms where

  -- "minimum wage is raised"
  postulate wages↑ : Set
  -- "mass layoffs happen"
  postulate layoffs : Set
  -- "unemployment goes up"
  postulate employment↓ : Set

module InferenceRules where
  open Axioms

  -- "if the minimum wage is raised, mass layoffs happen"
  postulate w→l : wages↑ → layoffs
  -- "if mass layoffs happen, unemployment goes up
  postulate l→e : layoffs → employment↓
  -- "if X raises unemployment, don't do X"
  postulate □¬employment↓ : {X : Set} →
                             (X → employment↓) →
                             --------------------
                             □ (¬ X)

module Argument where
  open Axioms
  open InferenceRules

  -- "don't raise the minimum wage"
  □¬wages↑ : □ (¬ wages↑)
  □¬wages↑ = □¬employment↓ (l→e ∘ w→l)

module RefactoredPremise where
  open Axioms
  open InferenceRules

  -- "don't raise the minimum wage"
  □¬wages↑ : □ (¬ wages↑)
  □¬wages↑ = □¬employment↓ w→e
    where
      -- "if the minimum wage is raised, unemployment goes up"
      w→e : wages↑ → employment↓
      w→e = l→e ∘ w→l
