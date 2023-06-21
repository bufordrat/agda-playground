module FOL where

open import Data.Product
open import Data.Sum

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
teller2-5-2-e = {!!}
