/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.FiniteRootPowerExpansion

/-!
# A common integral counting profile for all actual Jacobi power twists

The exact field-size-minus-two mass retains both zero-coordinate corrections.
The principal twist is included using its actual Jacobi value, rather than
replacing the zero values of the underlying function by zeroth powers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.JacobiPower

theorem actual_counting_profile {F : Type*} [Field F] [Fintype F]
    (n : Nat) [NeZero n] (chi psi : MulChar F Complex) (z : Complex)
    (hz : IsPrimitiveRoot z n) (hchi : chi ^ n = 1)
    (hpsi : psi ^ n = 1) :
    Exists fun v : Fin n -> Nat =>
      (Finset.univ.sum v = Fintype.card F - 2) /\
      (forall r : Nat, jacobiSum (chi ^ r) (psi ^ r) =
        Finset.univ.sum (fun j => (v j : Complex) * (z ^ j.val) ^ r)) := by
  classical
  let f : F -> Complex := fun x => chi x * psi (1 - x)
  have hroot : forall x : F, f x = 0 \/
      Exists fun j : Fin n => f x = z ^ j.val := by
    intro x
    by_cases hfx : f x = 0
    . exact Or.inl hfx
    . apply Or.inr
      have hxne : Not (chi x = 0) := by
        intro hzero
        apply hfx
        dsimp [f]
        rw [hzero, zero_mul]
      have hyne : Not (psi (1 - x) = 0) := by
        intro hzero
        apply hfx
        dsimp [f]
        rw [hzero, mul_zero]
      have hux : IsUnit x := chi.apply_ne_zero_iff.mp hxne
      have huy : IsUnit (1 - x) := psi.apply_ne_zero_iff.mp hyne
      have hxn : chi x ^ n = 1 := by
        have h := congrArg (fun theta : MulChar F Complex => theta x) hchi
        simpa only [chi.pow_apply' (NeZero.ne n) x,
          MulChar.one_apply hux] using h
      have hyn : psi (1 - x) ^ n = 1 := by
        have h := congrArg (fun theta : MulChar F Complex => theta (1 - x)) hpsi
        simpa only [psi.pow_apply' (NeZero.ne n) (1 - x),
          MulChar.one_apply huy] using h
      have hfn : f x ^ n = 1 := by
        dsimp [f]
        rw [mul_pow, hxn, hyn, one_mul]
      cases hz.eq_pow_of_pow_eq_one hfn with
      | intro j hj =>
        exact Exists.intro (Fin.mk j hj.1) hj.2.symm
  cases FiniteRootPower.exists_counting_profile n f z hroot
      (Finset.univ : Finset F) with
  | intro v hv =>
    have hfilter :
        (Finset.univ.filter fun x : F => Not (f x = 0)) =
          (Finset.univ \ {0, 1}) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and]
      change Not (chi x * psi (1 - x) = 0) <->
        Not (x = 0 \/ x = 1)
      constructor
      . intro hprod hor
        have hxne : Not (chi x = 0) := by
          intro hzero
          apply hprod
          rw [hzero, zero_mul]
        have hyne : Not (psi (1 - x) = 0) := by
          intro hzero
          apply hprod
          rw [hzero, mul_zero]
        have hux : IsUnit x := chi.apply_ne_zero_iff.mp hxne
        have huy : IsUnit (1 - x) := psi.apply_ne_zero_iff.mp hyne
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
        | inr hzero => exact (psi.apply_ne_zero_iff.mpr huy) hzero
    have hmass : Finset.univ.sum v = Fintype.card F - 2 := by
      rw [hv.1, hfilter,
        Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Finset.card_pair zero_ne_one]
    have hcard : 2 <= Fintype.card F :=
      Nat.add_one_le_of_lt Fintype.one_lt_card
    apply Exists.intro v
    apply And.intro hmass
    intro r
    by_cases hr : r = 0
    . subst r
      simp only [pow_zero, mul_one]
      rw [jacobiSum_one_one, <- Nat.cast_sum, hmass,
        Nat.cast_sub hcard, Nat.cast_two]
    . have hpositive : 0 < r := Nat.pos_of_ne_zero hr
      calc
        jacobiSum (chi ^ r) (psi ^ r) =
            (Finset.univ : Finset F).sum (fun x => f x ^ r) := by
          unfold jacobiSum
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [f]
          rw [chi.pow_apply' hr x, psi.pow_apply' hr (1 - x), mul_pow]
        _ = Finset.univ.sum
            (fun j => (v j : Complex) * (z ^ j.val) ^ r) :=
          hv.2 r hpositive

theorem inverse_symmetry {F : Type*} [Field F] [Fintype F]
    (chi psi : MulChar F Complex) :
    jacobiSum chi psi =
      psi (-1) * jacobiSum (Inv.inv (chi * psi)) psi := by
  classical
  have hinv : jacobiSum chi psi =
      (Finset.univ : Finset F).sum
        (fun x => chi (Inv.inv x) * psi (1 - (Inv.inv x))) := by
    unfold jacobiSum
    apply Finset.sum_bij (fun x _ => (Inv.inv x))
    . intro x hx
      exact Finset.mem_univ _
    . intro x hx y hy hxy
      exact inv_injective hxy
    . intro y hy
      exact Exists.intro (Inv.inv y)
        (Exists.intro (Finset.mem_univ _) (inv_inv y))
    . intro x hx
      rw [inv_inv]
  rw [hinv]
  unfold jacobiSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxzero : x = 0
  . subst x
    simp only [inv_zero, chi.map_nonunit not_isUnit_zero,
      (Inv.inv (chi * psi)).map_nonunit not_isUnit_zero, zero_mul, mul_zero]
  . have harg : 1 - (Inv.inv x) = (-1) * (1 - x) * (Inv.inv x) := by
      calc
        1 - (Inv.inv x) = x * (Inv.inv x) - (Inv.inv x) := by
          rw [<- div_eq_mul_inv, div_self hxzero]
        _ = (-1) * (1 - x) * (Inv.inv x) := by ring
    rw [harg, map_mul, map_mul, MulChar.inv_apply', MulChar.mul_apply]
    ring

end Metaplectic.JacobiPower
