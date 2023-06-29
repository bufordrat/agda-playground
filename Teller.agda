module Teller where

open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Data.Empty
open import Agda.Primitive



module 2-5-1-a where

    -- Teller Volume 2, Chap. 5, exercise 1a

    --  Prove:
    --   (∀x)(Px & Dx)
    --   --------n
    --   Pk

    implicit : {Domain : Set}
               {k : Domain} →
               {P D : Domain → Set} → 
               (∀ (x : Domain) → P x × D x) →
               -------------
               P k

    implicit prf with prf _
    ... | (pk , dk) = pk

    explicit : (Domain : Set)
               (k : Domain) →
               (P D : Domain → Set) → 
               (∀ (x : Domain) → P x × D x) →
               -------------
               P k

    explicit Domain k P D prf with prf k
    ... | (pk , dk) = pk


module 2-5-1-c where

    -- Teller Volume 2, Chap. 5, exercise 1c

    --  Prove:
    --   (∀x)(Dx → Kx)
    --   (∀x)Dx
    --   -------
    --   Ka

    implicit : {Domain : Set} →
               {a : Domain} →
               {K D : Domain → Set} → 
               (∀ (x : Domain) → D x → K x) →
               (∀ (x : Domain) → D x) →
               -------------
               K a

    implicit wide_prf
             narrow_prf
             with (wide_prf _ , narrow_prf _)
    ... | (cond , da) = cond da

    explicit : (Domain : Set) →
               (a : Domain) →
               (K D : Domain → Set) → 
               (∀ (x : Domain) → D x → K x) →
               (∀ (x : Domain) → D x) →
               -------------
               K a

    explicit Domain
             a
             K
             D
             wide_prf
             narrow_prf
             with (wide_prf a , narrow_prf a)
    ... | (cond , da) = cond da


module 2-5-1-d-nonempty where

    -- Teller Volume 2, Chap. 5, exercise 1d

    --  Prove:
    --   (∀x)(Mx → A)
    --   --------
    --   (∀x)Mx → A

    -- If you add the assumption that Domain is inhabited, this
    -- inference works.  Without it, see the next exercise!
    
    explicit : (Domain A : Set) →
               (M : Domain → Set) →
               (wit : Domain) →
               (∀ (x : Domain) → (M x → A)) →
               (∀ (x : Domain) → M x) →
               -------------
               A

    explicit Domain A M wit wide_prf narrow_prf = a
      where
        m_wit_a : M wit → A
        m_wit_a = wide_prf wit

        m_wit : M wit
        m_wit = narrow_prf wit

        a : A
        a = m_wit_a m_wit


module 2-5-1-d where

    -- What Teller Volume 2, Chap. 5, exercise 1d ought to have been,
    -- in a just intuitionist world.

    --  Prove:
    --   (∀x)(Mx → A)
    --   (∀x)Mx → A
    --   --------
    --   ⊥

    2-1-5-d : Set₁
    2-1-5-d = (Domain A : Set₀) →
              (M : Domain → Set₀) →
              (∀ (x : Domain) → M x → A) →
              (∀ (x : Domain) → M x) →
              -------------
              A

    nope : 2-1-5-d → ⊥
    nope prf = prf Domain A M all_mx_a all_mx
      where
        Domain = ⊥
        A = ⊥
        M = ⊥-elim
        all_mx_a = λ x _ → M x
        all_mx = λ x → M x


module 2-5-1-h where

    -- Teller Volume 2, Chap. 5, exercise 1h

    --  Prove:
    --   (∀x)(Rxx ∨ Rxk)
    --   (∀y)~Ryk
    --   --------
    --   Rcc & Rff

    explicit : (Domain : Set) →
               (R : Domain → Domain → Set) →
               (c f k : Domain) →
               (∀ (x : Domain) -> R x x ⊎ R x k) →
               (∀ (y : Domain) -> ¬ R y k) →
               -------------
               R c c × R f f

    explicit Domain R c f k univ_disj univ_neg = conclusion
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

    implicit : {Domain : Set} →
               {N G : Domain → Set} →
               {a : Domain} →
               N a →
               -------------
               ∃[ x ] (N x ⊎ G x)

    implicit na = (_ , inj₁ na)

    explicit : (Domain : Set) →
               (N G : Domain → Set) →
               (a : Domain) →
               N a →
               -------------
               ∃[ x ] (N x ⊎ G x)

    explicit Domain N G a na = (a , inj₁ na)

module 2-5-2-e where

    -- Teller Volume 2, Chap. 5, exercise 2e

    --  Prove:
    --   Fa ∨ Nh
    --   -------
    --   (∃x)Fx ∨ (∃x)Nx

    implicit : {Domain : Set} →
               {F N : Domain → Set} →
               {a : Domain} → 
               {h : Domain} →
               F a ⊎ N h →
               -------------
               ∃[ x ] F x ⊎ ∃[ x ] N x

    implicit (inj₁ fa) = inj₁ (_ , fa)
    implicit (inj₂ nh) = inj₂ (_ , nh)

    explicit : (Domain : Set) →
               (F N : Domain → Set) →
               (a : Domain) → 
               (h : Domain) →
               F a ⊎ N h →
               -------------
               ∃[ x ] F x ⊎ ∃[ x ] N x

    explicit Domain F N a h (inj₁ fa) = inj₁ (a , fa)
    explicit Domain F N a h (inj₂ nh) = inj₂ (h , nh)



module 2-5-2-g where

    -- Teller Volume 2, Chap. 5, exercise 2g

    --  Prove:
    --   (∃x)Rxa → (∀x)Rax
    --   Rea
    --   -------
    --   (∃x)Rax

    explicit : (Domain : Set) →
               (R : Domain → Domain → Set) →
               (a : Domain) →
               (e : Domain) →
               (∃[ x ] R x a -> ∀ (x : Domain) → R a x) →
               R e a →
               -------------
               ∃[ x ] R a x

    explicit Domain R a e ex_to_univ rea = ex_rae
      where
        ex_rea : ∃[ x ] R x a
        ex_rea = (e , rea)

        univ : ∀ (x : Domain) → R a x
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

    implicit : {Domain : Set} →
               {J : Domain → Set} →
               {Q : Set} →
               ∃[ x ] (J x → Q) →
               -------------
               (∀ (x : Domain) → J x) →
               Q

    implicit (wit , cond) univ =
      cond (univ wit)

    explicit : (Domain : Set) →
               (J : Domain → Set) →
               (Q : Set) →
               ∃[ x ] (J x → Q) →
               -------------
               (∀ (x : Domain) → J x) →
               Q

    explicit Domain J Q (wit , cond) univ =
      cond (univ wit)

module 2-6-1-p where

  -- Teller Volume 2, Chap. 6, exercise 1p

  -- Prove:
  --   (∀x)Px → (∀x)Qx
  --   ------------------
  --   (∃x)(∀y)(Px → Qy)

  -- the infamous buttpain exercise

  -- 2-6-1-p : Set₁
  -- 2-6-1-p = (Domain : Set₀) →
  --           (P : Domain → Set₀) →
  --           (Q : Domain → Set₀) →
  --           (∀ (x : Domain) → P x) →
  --           (∀ (y : Domain) → Q y) →
  --           -------------------------
  --           Σ Domain (λ x → (∀ (y : Domain) → P x → Q y))

  -- nope : 2-6-1-p → ⊥
  -- nope prf = {!!}
  --   where
  --     Domain = ⊥
  --     P = ⊥-elim
  --     Q = ⊥-elim
  --     univ_p : ∀ (x : ⊥) → ⊥
  --     univ_p = ⊥-elim
  --     conc : Σ Domain (λ (x : ⊥) → ⊥ → ⊥ → ⊥)
  --     conc = prf Domain univ_p ? ?

module Metamath where

  -- Metamath Existential Quantifier Swap
  -- https://us.metamath.org/ileuni/19.12.html

  -- Prove:
  --   ∃x ∀y ϕ
  --   -------
  --   ∀y ∃x ϕ

  -- Shouldn't this be called "Existential Quantifier Push-in"?  That
  -- phrasing emphasizes the asymmetry of the rule.

  theorem-19-12 : {Domain : Set} →
                  {ϕ : Set} →
                  Σ Domain (λ x → (∀ (y : Domain) → ϕ)) →
                  ∀ (y : Domain) →
                  -------------
                  Σ Domain (λ x → ϕ)
  theorem-19-12 (x , yphi) y = (x , yphi y)

  theorem-19-12' : ∀ {i j k} →
                   {A : Set i} →
                   {B : Set j} →
                   {P : A → B → Set k} →
                   ----------
                   ∃[ x ] (∀ {y} → P x y) →
                   ∀ {y} → ∃[ x ] P x y
  theorem-19-12' (x , y_pxy) = (x , y_pxy)

  -- converse : Set uhh-max-of-ijk-or-something
  -- converse = ∀ {i j k} →
  --            {A : Set i} →
  --            {B : Set j} →
  --            {P : A → B → Set k} →
  --            ----------
  --            ∀ {y} → ∃[ x ] P x y →
  --            ∃[ x ] (∀ {y} → P x y)

  -- converse-is-bad : converse → ⊥
  -- converse-is-bad prf = destruct univ_narrow
  --   where
  --     Domain = ⊥
  --     ϕ = ⊥
  --     univ_wide = ⊥-elim
  --     univ_narrow_type = Σ Domain (λ x → ∀ (y : Domain) → ϕ)
  --     univ_narrow = prf Domain ϕ univ_wide
  --     destruct : univ_narrow_type → ⊥
  --     destruct (wit , all_phi) = all_phi wit

