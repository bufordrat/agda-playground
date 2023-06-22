module Teller where

open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Data.Empty



module 2-5-1-a where

    -- Teller Volume 2, Chap. 5, exercise 1a

    --  Prove:
    --   (∀x)(Px & Dx)
    --   --------
    --   Pk

    implicit : {Carrier : Set}
               {k : Carrier} →
               {P D : Carrier → Set} → 
               (∀ (x : Carrier) → P x × D x) →
               -------------
               P k

    implicit prf with prf _
    ... | (pk , dk) = pk

    explicit : (Carrier : Set)
               (k : Carrier) →
               (P D : Carrier → Set) → 
               (∀ (x : Carrier) → P x × D x) →
               -------------
               P k

    explicit Carrier k P D prf with prf k
    ... | (pk , dk) = pk


module 2-5-1-c where

    -- Teller Volume 2, Chap. 5, exercise 1c

    --  Prove:
    --   (∀x)(Dx → Kx)
    --   (∀x)Dx
    --   -------
    --   Ka

    implicit : {Carrier : Set} →
               {a : Carrier} →
               {K D : Carrier → Set} → 
               (∀ (x : Carrier) → D x → K x) →
               (∀ (x : Carrier) → D x) →
               -------------
               K a

    implicit wide_prf
             narrow_prf
             with (wide_prf _ , narrow_prf _)
    ... | (cond , da) = cond da

    explicit : (Carrier : Set) →
               (a : Carrier) →
               (K D : Carrier → Set) → 
               (∀ (x : Carrier) → D x → K x) →
               (∀ (x : Carrier) → D x) →
               -------------
               K a

    explicit Carrier
             a
             K
             D
             wide_prf
             narrow_prf
             with (wide_prf a , narrow_prf a)
    ... | (cond , da) = cond da


module 2-5-1-d where

    -- Teller Volume 2, Chap. 5, exercise 1d

    --  Prove:
    --   (∀x)(Mx → A)
    --   --------
    --   (∀x)Mx → A

    -- Hmm, stuck on this one; is that because this inference is only
    -- good in classical logic?

    -- UPDATE: hmm, I guess it works if you add this a thing, which is
    -- effectively introducing Teller's assumption that Carrier is
    -- inhabited...

    explicit : (Carrier A : Set) →
               (M : Carrier → Set) →
               (a : Carrier) →
               (∀ (x : Carrier) → (M x → A)) →
               (∀ (x : Carrier) → M x) →
               -------------
               A

    explicit Carrier A M a wide_prf narrow_prf = {!!}
      where
        mxa : M a → A
        mxa = {!!}


module 2-5-1-h where

    -- Teller Volume 2, Chap. 5, exercise 1h

    --  Prove:
    --   (∀x)(Rxx ∨ Rxk)
    --   (∀y)~Ryk
    --   --------
    --   Rcc & Rff

    explicit : (Carrier : Set) →
               (R : Carrier → Carrier → Set) →
               (c f k : Carrier) →
               (∀ (x : Carrier) -> R x x ⊎ R x k) →
               (∀ (y : Carrier) -> ¬ R y k) →
               -------------
               R c c × R f f

    explicit Carrier R c f k univ_disj univ_neg = conclusion
      where
        univ_disj_c : R c c ⊎ R c k
        univ_disj_c = univ_disj c

        univ_disj_f : R f f ⊎ R f k
        univ_disj_f = univ_disj f

        not_rfk : ¬ R f k
        not_rfk = univ_neg f

        not_rck : ¬ R c k
        not_rck = univ_neg c

        disj_c_elim : R c c ⊎ R c k → R c c
        disj_c_elim (inj₁ rcc) = rcc
        disj_c_elim (inj₂ rck) = ⊥-elim (not_rck rck)

        disj_f_elim : R f f ⊎ R f k -> R f f
        disj_f_elim (inj₁ rff) = rff
        disj_f_elim (inj₂ rfk) = ⊥-elim (not_rfk rfk)

        rcc : R c c
        rcc = disj_c_elim univ_disj_c

        rff : R f f
        rff = disj_f_elim univ_disj_f

        conclusion : R c c × R f f
        conclusion = (rcc , rff)


module 2-5-2-a where

    -- Teller Volume 2, Chap. 5, exercise 2a


    --  Prove:
    --   Na
    --   -------
    --   (∃x)(Nx ∨ Gx)

    implicit : {Carrier : Set} →
               {N G : Carrier → Set} →
               {a : Carrier} →
               N a →
               -------------
               ∃[ x ] (N x ⊎ G x)

    implicit na = (_ , inj₁ na)


module 2-5-2-e where

    -- Teller Volume 2, Chap. 5, exercise 2e

    --  Prove:
    --   Fa ∨ Nh
    --   -------
    --   (∃x)Fx ∨ (∃x)Nx

    implicit : {Carrier : Set} →
               {F N : Carrier → Set} →
               {a : Carrier} → 
               {h : Carrier} →
               F a ⊎ N h →
               -------------
               ∃[ x ] F x ⊎ ∃[ x ] N x

    implicit (inj₁ fa) = inj₁ (_ , fa)
    implicit (inj₂ nh) = inj₂ (_ , nh)


module 2-5-2-g where

    -- Teller Volume 2, Chap. 5, exercise 2g

    --  Prove:
    --   (∃x)Rxa → (∀x)Rax
    --   Rea
    --   -------
    --   (∃x)Rax

    explicit : (Carrier : Set) →
               (R : Carrier → Carrier → Set) →
               (a : Carrier) →
               (e : Carrier) →
               (∃[ x ] R x a -> ∀ (x : Carrier) → R a x) →
               R e a →
               -------------
               ∃[ x ] R a x

    explicit Carrier R a e ex_to_univ rea = ex_rae
      where
        ex_rea : ∃[ x ] R x a
        ex_rea = (e , rea)

        univ : ∀ (x : Carrier) → R a x
        univ = ex_to_univ ex_rea

        rae : R a e
        rae = univ e

        ex_rae : ∃[ x ] R a x
        ex_rae = (e , rae)


module 2-5-2-i where

    -- Teller Volume 2, Chap. 5, exercise 2i

    --  Prove:
    --   (∃x)Jx → Q
    --   (∀x)Jx
    --   -------
    --   Q

    implicit : {Carrier : Set} →
               {J : Carrier → Set} →
               {Q : Set} →
               ∃[ x ] (J x → Q) →
               -------------
               (∀ (x : Carrier) → J x) →
               Q

    implicit (wit , cond) univ =
      cond (univ wit)


