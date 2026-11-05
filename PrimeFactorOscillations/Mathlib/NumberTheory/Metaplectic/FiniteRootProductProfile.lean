/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.FiniteRootPowerExpansion
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.JacobiPowerProfile

/-!
# One root-counting profile also preserves the full supported product

The same natural vector records every positive power sum and the product.
The product information supplies the first-moment congruence of the actual
Jacobi profile; it cannot be inferred from a semiring power-sum witness alone.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FiniteRootPower

theorem exists_counting_product_profile
    {R : Type*} [CommSemiring R] [DecidableEq R]
    {I : Type*} (n : Nat) (f : I -> R) (z : R)
    (hf : forall x : I, f x = 0 \/
      Exists fun j : Fin n => f x = z ^ j.val)
    (S : Finset I) :
    Exists fun v : Fin n -> Nat =>
      (Finset.univ.sum v = (S.filter fun x => Not (f x = 0)).card) /\
      (forall r : Nat, 0 < r ->
        S.sum (fun x => f x ^ r) =
          Finset.univ.sum (fun j => (v j : R) * (z ^ j.val) ^ r)) /\
      ((S.filter fun x => Not (f x = 0)).prod f =
        Finset.univ.prod (fun j => (z ^ j.val) ^ v j)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    apply Exists.intro (fun _ => 0)
    constructor
    . simp
    . constructor
      . intro r hr
        simp
      . simp
  | @insert x S hx ih =>
    cases ih with
    | intro v hv =>
      by_cases hfx : f x = 0
      . apply Exists.intro v
        constructor
        . simpa [Finset.filter_insert, hfx] using hv.1
        . constructor
          . intro r hr
            rw [Finset.sum_insert hx, hfx, zero_pow (Nat.ne_of_gt hr), zero_add]
            exact hv.2.1 r hr
          . simpa [Finset.filter_insert, hfx] using hv.2.2
      . cases Or.resolve_left (hf x) hfx with
        | intro j hj =>
          let w : Fin n -> Nat := fun i => v i + if i = j then 1 else 0
          have hnot : Not (Membership.mem
              (S.filter fun t => Not (f t = 0)) x) := by
            intro hmem
            exact hx (Finset.mem_filter.mp hmem).1
          apply Exists.intro w
          constructor
          . simp [w, Finset.sum_add_distrib, Finset.filter_insert,
              hfx, hnot, hv.1, add_comm]
          . constructor
            . intro r hr
              rw [Finset.sum_insert hx, hj, hv.2.1 r hr]
              simp [w, add_mul, Finset.sum_add_distrib, add_comm]
            . rw [Finset.filter_insert, ite_eq_left hfx,
                Finset.prod_insert hnot, hj, hv.2.2]
              have hpow (i : Fin n) : (z ^ i.val) ^ w i =
                  (z ^ i.val) ^ v i * (if i = j then z ^ j.val else 1) := by
                by_cases hi : i = j
                . subst i
                  simp [w, pow_add]
                . simp [w, hi]
              simp_rw [hpow]
              rw [Finset.prod_mul_distrib]
              simp [mul_comm]

end FiniteRootPower

namespace Metaplectic.JacobiPower

theorem diagonal_supported_product {F : Type*} [Field F] [Fintype F]
    [DecidableEq F]
    (chi : MulChar F Complex) :
    ((Finset.univ \ {0, 1}) : Finset F).prod
      (fun x => chi x * chi (1 - x)) = 1 := by
  classical
  let S : Finset F := Finset.univ \ {0, 1}
  have hmem (x : F) : Membership.mem S x <->
      Not (x = 0) /\ Not (x = 1) := by
    simp [S, not_or]
  have hsub (x : F) (hx : Membership.mem S x) :
      Membership.mem S (1 - x) := by
    have h := (hmem x).mp hx
    apply (hmem (1 - x)).mpr
    constructor
    . intro he
      apply h.2
      exact (sub_eq_zero.mp he).symm
    . intro he
      apply h.1
      calc
        x = 1 - (1 - x) := by ring
        _ = 0 := by rw [he, sub_self]
  have hinvMem (x : F) (hx : Membership.mem S x) :
      Membership.mem S (Inv.inv x) := by
    have h := (hmem x).mp hx
    apply (hmem (Inv.inv x)).mpr
    constructor
    . exact inv_ne_zero h.1
    . intro he
      apply h.2
      have ht := congrArg Inv.inv he
      simpa only [inv_inv, inv_one] using ht
  have hsubProd : S.prod chi = S.prod (fun x => chi (1 - x)) := by
    apply Finset.prod_bij (fun x _ => 1 - x)
    . intro x hx
      exact hsub x hx
    . intro x hx y hy hxy
      calc
        x = 1 - (1 - x) := by ring
        _ = 1 - (1 - y) := by rw [hxy]
        _ = y := by ring
    . intro y hy
      exact Exists.intro (1 - y)
        (Exists.intro (hsub y hy) (by ring))
    . intro x hx
      congr 1
      ring
  have hinvProd : S.prod chi = S.prod (fun x => chi (Inv.inv x)) := by
    apply Finset.prod_bij (fun x _ => Inv.inv x)
    . intro x hx
      exact hinvMem x hx
    . intro x hx y hy hxy
      exact inv_injective hxy
    . intro y hy
      exact Exists.intro (Inv.inv y)
        (Exists.intro (hinvMem y hy) (inv_inv y))
    . intro x hx
      rw [inv_inv]
  have hsquare : S.prod chi * S.prod chi = 1 := by
    calc
      S.prod chi * S.prod chi =
          S.prod chi * S.prod (fun x => chi (Inv.inv x)) := by rw [<- hinvProd]
      _ = S.prod (fun x => chi x * chi (Inv.inv x)) := by
        rw [Finset.prod_mul_distrib]
      _ = S.prod (fun _ => (1 : Complex)) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hx0 := ((hmem x).mp hx).1
        have hcancel : x * Inv.inv x = 1 := by field_simp [hx0]
        rw [<- map_mul, hcancel, map_one]
      _ = 1 := by simp
  change S.prod (fun x => chi x * chi (1 - x)) = 1
  calc
    _ = S.prod chi * S.prod (fun x => chi (1 - x)) := by
      rw [Finset.prod_mul_distrib]
    _ = S.prod chi * S.prod chi := by rw [<- hsubProd]
    _ = 1 := hsquare


/-- Actual diagonal Jacobi twists share their full root product as well as all moments. -/
theorem actual_diagonal_counting_product_profile
    {F : Type*} [Field F] [Fintype F]
    (n : Nat) [NeZero n] (chi : MulChar F Complex) (z : Complex)
    (hz : IsPrimitiveRoot z n) (hchi : chi ^ n = 1) :
    Exists fun v : Fin n -> Nat =>
      (Finset.univ.sum v = Fintype.card F - 2) /\
      (forall r : Nat, jacobiSum (chi ^ r) (chi ^ r) =
        Finset.univ.sum (fun j => (v j : Complex) * (z ^ j.val) ^ r)) /\
      (Finset.univ.prod (fun j => (z ^ j.val) ^ v j) = 1) := by
  classical
  let f : F -> Complex := fun x => chi x * chi (1 - x)
  have hval (y : F) (hy : IsUnit y) : chi y ^ n = 1 := by
    have ht := congrArg (fun theta : MulChar F Complex => theta y) hchi
    simpa only [chi.pow_apply' (NeZero.ne n) y, MulChar.one_apply hy] using ht
  have hroot : forall x : F, f x = 0 \/
      Exists fun j : Fin n => f x = z ^ j.val := by
    intro x
    by_cases hfx : f x = 0
    . exact Or.inl hfx
    . apply Or.inr
      have hxy : Not (chi x = 0) /\ Not (chi (1 - x) = 0) := by
        change Not (chi x * chi (1 - x) = 0) at hfx
        exact mul_ne_zero_iff.mp hfx
      have hpow : f x ^ n = 1 := by
        dsimp [f]
        rw [mul_pow, hval x (chi.apply_ne_zero_iff.mp hxy.1),
          hval (1 - x) (chi.apply_ne_zero_iff.mp hxy.2), one_mul]
      cases hz.eq_pow_of_pow_eq_one hpow with
      | intro j hj =>
        exact Exists.intro (Fin.mk j hj.1) hj.2.symm
  cases FiniteRootPower.exists_counting_product_profile n f z hroot
      (Finset.univ : Finset F) with
  | intro v hv =>
    have hfilter :
        (Finset.univ.filter fun x : F => Not (f x = 0)) =
          (Finset.univ \ {0, 1}) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and]
      change Not (chi x * chi (1 - x) = 0) <->
        Not (x = 0 \/ x = 1)
      constructor
      . intro hprod hor
        have hxne : Not (chi x = 0) := by
          intro hzero
          apply hprod
          rw [hzero, zero_mul]
        have hyne : Not (chi (1 - x) = 0) := by
          intro hzero
          apply hprod
          rw [hzero, mul_zero]
        have hux : IsUnit x := chi.apply_ne_zero_iff.mp hxne
        have huy : IsUnit (1 - x) := chi.apply_ne_zero_iff.mp hyne
        cases hor with
        | inl hxzero =>
          exact (isUnit_iff_ne_zero.mp hux) hxzero
        | inr hxone =>
          have hyzero : 1 - x = 0 := by rw [hxone, sub_self]
          exact (isUnit_iff_ne_zero.mp huy) hyzero
      . intro hnot hprod
        have hux : IsUnit x := isUnit_iff_ne_zero.mpr
          (fun heq => hnot (Or.inl heq))
        have huy : IsUnit (1 - x) := isUnit_iff_ne_zero.mpr
          (fun heq => hnot (Or.inr (sub_eq_zero.mp heq).symm))
        cases mul_eq_zero.mp hprod with
        | inl hzero => exact (chi.apply_ne_zero_iff.mpr hux) hzero
        | inr hzero => exact (chi.apply_ne_zero_iff.mpr huy) hzero
    have hmass : Finset.univ.sum v = Fintype.card F - 2 := by
      rw [hv.1, hfilter,
        Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Finset.card_pair zero_ne_one]
    have hcard : 2 <= Fintype.card F :=
      Nat.add_one_le_of_lt Fintype.one_lt_card
    apply Exists.intro v
    constructor
    . exact hmass
    . constructor
      . intro r
        by_cases hr : r = 0
        . subst r
          simp only [pow_zero, mul_one]
          rw [jacobiSum_one_one, <- Nat.cast_sum, hmass,
            Nat.cast_sub hcard, Nat.cast_two]
        . calc
            jacobiSum (chi ^ r) (chi ^ r) =
                (Finset.univ : Finset F).sum (fun x => f x ^ r) := by
              unfold jacobiSum
              apply Finset.sum_congr rfl
              intro x hx
              dsimp [f]
              rw [chi.pow_apply' hr x, chi.pow_apply' hr (1 - x), mul_pow]
            _ = Finset.univ.sum
                (fun j => (v j : Complex) * (z ^ j.val) ^ r) :=
              hv.2.1 r (Nat.pos_of_ne_zero hr)
      . rw [<- hv.2.2, hfilter]
        exact diagonal_supported_product chi

end Metaplectic.JacobiPower
