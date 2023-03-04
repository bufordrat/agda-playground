module Chapter1 where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

record BooleanRing : Set₁ where
  field
    Carrier : Set₀
    _∙_ : Carrier → Carrier → Carrier
    _+_ : Carrier → Carrier → Carrier
    ¬ : Carrier → Carrier
    𝟙 : Carrier
    ∅ : Carrier
    +-assoc : ∀ { p q r } → (p + q) + r ≡ p + (q + r)
    +-comm : ∀ { p q } → p + q ≡ q + p
    +-id : ∀ { p } → p + ∅ ≡ p
    +-inverse : ∀ { p } → p + ¬ p ≡ ∅
    ∙-assoc : ∀ { p q r } → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
    ∙-left-id : ∀ { p } → p ∙ 𝟙 ≡ p
    ∙-right-id : ∀ { p } → 𝟙 ∙ p ≡ p
    left-distrib : ∀ { p q r } → p ∙ (q + r) ≡ (p ∙ q) + (p ∙ r)
    right-distrib : ∀ { p q r } → (q + r) ∙ p ≡ (q ∙ p) + (r ∙ p)
    ∙-idemp : ∀ { p } → p ∙ p ≡ p
  infixr 30 _∙_
  infixr 20 _+_


module Theorems (B : BooleanRing) where

  -- what to show: every Boolean ring has characteristic two, that is,
  -- any element p is its own additive inverse: p + p ≡ ∅

  open BooleanRing B

  -- first part of Halmos and Givant's proof

  -- x + y ≡ (x + y) ∙ (x + y)				idempotence
  --       ≡ ((x ∙ (x + y)) + (y ∙ (x + y)))		right-distributivity
  --       ≡ ((x ∙ x) + (x ∙ y)) + ((y ∙ x) + (y ∙ y))	left-distributivity
  --       ≡ x + (x ∙ y) + (y ∙ x) + y	      		idempotence

  foil-rule : ∀ { p q : Carrier } → p + q ≡ p + p ∙ q + q ∙ p + q
  foil-rule { p } { q } =
    begin
      p + q
    ≡⟨ sym ∙-idemp ⟩
      (p + q) ∙ (p + q)
    ≡⟨ right-distrib ⟩
      (p ∙ (p + q)) + (q ∙ (p + q))
    ≡⟨ cong (λ z → z + (q ∙ (p + q))) left-distrib ⟩
      (p ∙ p + p ∙ q) + (q ∙ (p + q))
    ≡⟨ cong (λ z → (p ∙ p + p ∙ q) + z) left-distrib ⟩
      (p ∙ p + p ∙ q) + (q ∙ p + q ∙ q)
    ≡⟨ cong (λ z → z + q ∙ p + q ∙ q) (cong (λ y → y + p ∙ q) ∙-idemp) ⟩
      (p + p ∙ q) + q ∙ p + q ∙ q
    ≡⟨ cong (λ z → (p + p ∙ q) + z) (cong (λ y → q ∙ p + y) ∙-idemp) ⟩
      (p + p ∙ q) + q ∙ p + q
    ≡⟨ +-assoc ⟩
      p + p ∙ q + q ∙ p + q
    ∎

  cancel-right : ∀ { p q r : Carrier } → p + q ≡ r + q → p ≡ r
  cancel-right { p } { q } { r } prf =
    begin
      p
    ≡⟨ sym +-id ⟩
      p + ∅
    ≡⟨ cong (λ z → p + z) (sym (+-inverse { q })) ⟩
      p + q + ¬ q
    ≡⟨ sym +-assoc ⟩
      (p + q) + ¬ q
    ≡⟨ cong (λ z → z + ¬ q) prf ⟩
      (r + q) + ¬ q
    ≡⟨ +-assoc ⟩
      r + q + ¬ q
    ≡⟨ cong (λ z → r + z) (+-inverse { q }) ⟩
      r + ∅
    ≡⟨ +-id ⟩
      r
    ∎

  cancel-left : ∀ { p q r : Carrier } → q + p ≡ q + r → p ≡ r
  cancel-left { p } { q } { r }
              rewrite (+-comm { q } { p }) | (+-comm { q } { r }) =
              cancel-right

  -- second part of Givant and Halmos proof

  -- y ≡ (x ∙ y) + (y ∙ x) + y	      			subtract x from both sides
  -- 0 ≡ (x ∙ y) + (y ∙ x)	      			subtract y from both sides
  --   ≡ (x ∙ x) + (x + x)				substitute x for y
  --   ≡ x + x						idempotence

  cancel-last-one-standing : ∀ { p r : Carrier } → p ≡ r + p → ∅ ≡ r
  cancel-last-one-standing { p } { r } prf = conclusion
    where
      add-zero : p + ∅ ≡ p + r
      add-zero rewrite +-id { p } | +-comm { p } { r }= prf
      conclusion : ∅ ≡ r
      conclusion = cancel-left add-zero

  double-p-q : ∀ { p q : Carrier } → ∅ ≡ p ∙ q + q ∙ p
  double-p-q { p } { q } = equality
    where
      just-q : q ≡ (p ∙ q + q ∙ p) + q
      just-q =
        begin
          q
        ≡⟨ cancel-left foil-rule ⟩
          p ∙ q + q ∙ p + q
        ≡⟨ sym +-assoc ⟩
          (p ∙ q + q ∙ p) + q
        ∎
      equality : ∅ ≡ p ∙ q + q ∙ p
      equality = cancel-last-one-standing just-q

  characteristic-two : ∀ { p q r : Carrier } → p + p ≡ ∅
  characteristic-two { p } { q } { r } = 
    begin
      p + p
    ≡⟨ cong (λ z → z + p) (sym ∙-idemp) ⟩
      p ∙ p + p
    ≡⟨ cong (λ z → p ∙ p + z) (sym ∙-idemp) ⟩
      p ∙ p + p ∙ p
    ≡⟨ sym (double-p-q { p } { p }) ⟩
      ∅
    ∎


module NathanTheorems (B : BooleanRing) where

  open BooleanRing B

  +-inverse-is-unique : ∀ {x y} → x + y ≡ ∅ → y ≡ ¬ x
  +-inverse-is-unique {x} {y} prf =
    begin
      y
    ≡⟨ sym +-id ⟩
      y + ∅
    ≡⟨ +-comm ⟩
      ∅ + y
    ≡⟨ cong (λ z → z + y) (sym +-inverse) ⟩
      (x + ¬ x) + y
    ≡⟨ cong (λ z → z + y) +-comm ⟩
      (¬ x + x) + y
    ≡⟨ +-assoc ⟩
      ¬ x + (x + y)
    ≡⟨ cong (λ z → ¬ x + z) prf ⟩
      ¬ x + ∅
    ≡⟨ +-id ⟩
      ¬ x
    ∎

  ¬¬-is-id : ∀ {x : Carrier} → ¬ (¬ x) ≡ x
  ¬¬-is-id = sym (+-inverse-is-unique (trans +-comm +-inverse))

  characteristicTwo : ∀ {x : Carrier} → x + x ≡ ∅
  characteristicTwo {x} =
    begin
      x + x
    ≡⟨  sym +-id ⟩
      (x + x) + ∅
    ≡⟨ cong (λ z → (x + x) + z) (sym +-inverse) ⟩
      (x + x) + ((x + x) + ¬ (x + x))
    ≡⟨ sym +-assoc ⟩
      ((x + x) + (x + x)) + ¬ (x + x)
    ≡⟨ cong (λ z → ((z + z) + (z + z)) + ¬ (x + x)) (sym ∙-idemp) ⟩
      (((x ∙ x) + (x ∙ x)) + ((x ∙ x) + (x ∙ x))) + ¬ (x + x)
    ≡⟨ cong (λ z → (z + z) + ¬ (x + x)) (sym right-distrib) ⟩
      (((x + x) ∙ x) + ((x + x) ∙ x)) + ¬ (x + x)
    ≡⟨ cong (λ z → z + ¬ (x + x)) (sym left-distrib) ⟩
      ((x + x) ∙ (x + x)) + ¬ (x + x)
    ≡⟨ cong (λ z → z + ¬ (x + x)) ∙-idemp ⟩
      (x + x) + ¬ (x + x)
    ≡⟨ +-inverse ⟩
      ∅
    ∎

  inverse-is-id : ∀ {x} → ¬ x ≡ x
  inverse-is-id {x} = sym (+-inverse-is-unique characteristicTwo)

