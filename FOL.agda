module FOL where

open import Data.Product
open import Data.Sum
open import Relation.Nullary.Negation

-- Teller Volume 2, Chap. 5, exercise 1a
--  Prove:
--   (∀x)(Px & Dx)
--   ___
--   Pk

teller2-5-1-a : {Carrier : Set}
                {k : Carrier} →
                {P D : Carrier → Set} → 
                ((x : Carrier) → P x × D x) →
                P k
teller2-5-1-a {Carrier} {k} {P} {D} prf with prf k
... | (pk , dk) = pk


-- Teller Volume 2, Chap. 5, exercise 1c
--  Prove:
--   (∀x)(Dx → Kx)
--   (∀x)Dx
--   ___
--   Ka

teller2-5-1-c : {Carrier : Set} →
                {a : Carrier} →
                {K D : Carrier → Set} → 
                ((x : Carrier) → D x → K x) →
                ((x : Carrier) → D x) →
                K a
teller2-5-1-c {Carrier}
              {a}
              {K}
              {D}
              wide_prf
              narrow_prf
              with (wide_prf a , narrow_prf a)
... | (cond , da) = cond da


-- Teller Volume 2, Chap. 5, exercise 1d
--  Prove:
--   (∀x)(Mx → A)
--   ___
--   (∀x)Mx → A

-- Hmm, stuck on this one; is that because this inference is only good in
-- classical logic?

teller2-5-1-d : {Carrier A : Set} →
                {M : Carrier → Set} →
                ((x : Carrier) → (M x → A)) →
                ((x : Carrier) → M x) →
                A
teller2-5-1-d {Carrier}
              {A}
              wide_prf
              narrow_prf = {!!}


-- Teller Volume 2, Chap. 5, exercise 1h
--  Prove:
--   (∀x)(Rxx ∨ Rxk)
--   (∀y)~Ryk
--   ___
--   Rcc & Rff

teller2-5-1-h : {Carrier : Set} →
                {R : Carrier → Carrier → Set} →
                {c f k : Carrier} →
                ((x : Carrier) -> R x x ⊎ R x k) →
                ((y : Carrier) -> ¬ R y k) →
                R c c × R f f
teller2-5-1-h = {!!}


-- Teller Volume 2, Chap. 5, exercise 2a
--  Prove:
--   Na
--   ___
--   (∃x)(Nx ∨ Gx)

teller2-5-2-a : {Carrier : Set} →
                {N G : Carrier → Set} →
                {a : Carrier} →
                N a →
                Σ Carrier (λ x → N x ⊎ G x)
teller2-5-2-a {Carrier}
              {N}
              {G}
              {a}
              na = (a , inj₁ na)



-- Teller Volume 2, Chap. 5, exercise 2e
--  Prove:
--   Fa ∨ Nh
--   ___
--   (∃x)Fx ∨ (∃x)Nx

teller2-5-2-e : {Carrier : Set} →
                {F N : Carrier → Set} →
                {a : Carrier} → 
                {h : Carrier} →
                F a ⊎ N h →
                Σ Carrier (λ x → F x) ⊎ Σ Carrier (λ x → N x)
teller2-5-2-e {F} {N} {a} {h} (inj₁ fa) = inj₁ (_ , fa)
teller2-5-2-e {F} {N} {a} {h} (inj₂ nh) = inj₂ (_ , nh)



-- Teller Volume 2, Chap. 5, exercise 2g
--  Prove:
--   (∃x)Rxa → (∀x)Rax
--   Rea
--   ___
--   (∃x)Rax

teller2-5-2-g : {Carrier : Set} →
                {R : Carrier → Carrier → Set} →
                {a : Carrier} →
                {e : Carrier} →
                (Σ Carrier (λ x → R x a) → ((x : Carrier) → R a x)) →
                R e a →
                Σ Carrier (λ x → R a x)
teller2-5-2-g {Carrier} {R} {a} {e} ex_to_univ rea = ex_rae
  where
    ex_rea : Σ Carrier (λ x → R x a)
    ex_rea = (e , rea)

    univ : (x : Carrier) → R a x
    univ = ex_to_univ ex_rea

    rae : R a e
    rae = univ e

    ex_rae : Σ Carrier (λ x → R a x)
    ex_rae = (e , rae)


-- Teller Volume 2, Chap. 5, exercise 2i
--  Prove:
--   (∃x)Jx → Q
--   (∀x)Jx
--   ___
--   Q

teller2-5-2-i : {Carrier : Set} →
                {J : Carrier → Set} →
                {Q : Set} →
                Σ Carrier (λ x → J x → Q) →
                ((x : Carrier) → J x) →
                Q
teller2-5-2-i {Carrier} {J} {Q} (wit , cond) univ =
  cond (univ wit)

