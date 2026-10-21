/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderInverseCount

/-!
# Prime-value classes of exponentially growing sequences

The class contains actual prime values. Repeated sequence values are
counted once by the class, and no infinitude or injectivity is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem classPowerWeight_summable_of_sequence_cover
    (P : Set Nat) (f : Nat -> Nat) (s : Real)
    (hcover : forall p, Nat.Prime p -> Membership.mem P p -> exists n, f n = p)
    (hsum : Summable (fun n : Nat => (f n : Real) ^ (-s))) :
    Summable (classPowerWeight P s) := by
  classical
  let k : Nat -> Nat := fun p => if hp : exists n, f n = p then Nat.find hp else 0
  apply summable_of_sum_le (classPowerWeight_nonneg P s)
    (c := tsum (fun n : Nat => (f n : Real) ^ (-s)))
  intro u
  let v := u.filter (fun p => And (Nat.Prime p) (Membership.mem P p))
  have hk : forall p, Membership.mem v p -> f (k p) = p := by
    intro p hp
    have hd := (Finset.mem_filter.mp hp).2
    have he := hcover p hd.1 hd.2
    dsimp [k]
    rw [dite_eq_left he]
    exact Nat.find_spec he
  have hinj : Set.InjOn k v := by
    intro p hp q hq heq
    calc
      p = f (k p) := (hk p hp).symm
      _ = f (k q) := by rw [heq]
      _ = q := hk q hq
  have heq : u.sum (classPowerWeight P s) = v.sum (fun p => (p : Real) ^ (-s)) := by
    simp only [v, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rfl
  rw [heq]
  calc
    v.sum (fun p => (p : Real) ^ (-s)) =
        v.sum (fun p => (f (k p) : Real) ^ (-s)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hk p hp]
    _ = (v.image k).sum (fun n => (f n : Real) ^ (-s)) :=
      (Finset.sum_image (f := fun n : Nat => (f n : Real) ^ (-s)) hinj).symm
    _ <= tsum (fun n : Nat => (f n : Real) ^ (-s)) :=
      Summable.sum_le_tsum (v.image k)
        (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

theorem sequence_power_summable_of_eventual_exponential_growth
    (f : Nat -> Nat) (A C s : Real) (hA : 1 < A) (hC : 0 < C) (hs : 0 < s)
    (hgrowth : Filter.Eventually (fun n : Nat => C * A ^ n <= (f n : Real)) atTop) :
    Summable (fun n : Nat => (f n : Real) ^ (-s)) := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hq0 : 0 <= A ^ (-s) := Real.rpow_nonneg (le_of_lt hA0) _
  have hpower : 1 < A ^ s := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hA hs
  have hq1 : A ^ (-s) < 1 := by
    rw [Real.rpow_neg (le_of_lt hA0), <- one_div]
    exact (div_lt_one (Real.rpow_pos_of_pos hA0 s)).mpr hpower
  have hgeo : Summable (fun n : Nat => C ^ (-s) * (A ^ (-s)) ^ n) :=
    (summable_geometric_iff_norm_lt_one.mpr
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).mul_left (C ^ (-s))
  apply Summable.of_norm_bounded_eventually_nat hgeo
  filter_upwards [hgrowth] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    (f n : Real) ^ (-s) <= (C * A ^ n) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hC (pow_pos hA0 n)) hn (by linarith)
    _ = C ^ (-s) * (A ^ (-s)) ^ n := by
      rw [Real.mul_rpow (le_of_lt hC) (pow_nonneg (le_of_lt hA0) n),
        <- Real.rpow_pow_comm (le_of_lt hA0)]

theorem primeClassConvergenceExponent_zero_of_all_positive_summable
    (P : Set Nat) (hsum : forall s : Real, 0 < s -> Summable (classPowerWeight P s)) :
    primeClassConvergenceExponent P = 0 := by
  have htau0 := primeClassConvergenceExponent_nonneg P (1 / 2) (by norm_num) (hsum _ (by norm_num))
  apply le_antisymm _ htau0
  by_contra hnot
  have htau : 0 < primeClassConvergenceExponent P := lt_of_not_ge hnot
  have hhalf : 0 < primeClassConvergenceExponent P / 2 := by linarith
  have hle := primeClassConvergenceExponent_le P _ hhalf (hsum _ hhalf)
  linarith

theorem integerDecoderCapacity_top_of_all_positive_summable
    (P : Set Nat) (hsum : forall s : Real, 0 < s -> Summable (classPowerWeight P s)) :
    integerDecoderCapacity P = Top.top := by
  exact integerDecoderCapacity_eq_top_of_zero_convergenceExponent P (1 / 2)
    (by norm_num) (by norm_num) (hsum _ (by norm_num))
    (primeClassConvergenceExponent_zero_of_all_positive_summable P hsum)

end PrimeFactorOscillations.PrimeClassSampling
