/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzFrequencyTail

/-!
# CoprimeSchwartzMiddle

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.CoprimeSchwartzMiddle

open CoprimeSchwartzCenter CoprimeSchwartzSplit CoprimeSchwartzMixed
open CoprimeSchwartzLow SchwartzFrequencyTail

theorem middleDivisors_card (q : Nat) (hq : 0 < q) (Y Z : Real) (hZ : 0 <= Z) :
    ((middleDivisors q Y Z).card : Real) <= Z := by
  have hsub : middleDivisors q Y Z <= smallDivisors q Z := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr (And.intro h.1 h.2.2)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (smallDivisors_card q hq Z hZ)

theorem middleTail_row_bound (f : SchwartzMap Real Complex)
    (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (d L : Nat) (X : Real), 0 < d -> 1 <= L -> 0 < X ->
      norm ((ArithmeticFunction.moebius d : Complex) *
        ((X / (d : Real) : Real) : Complex) *
        frequencyTail L (FourierTransform.fourier f) (X / (d : Real))) <=
      C * ((d : Real) / X) ^ (k - 1) / (L : Real) ^ (k - 1) := by
  choose C hC hc using frequencyTail_norm_bound (FourierTransform.fourier f) k hk
  refine Exists.intro C (And.intro hC ?_)
  intro d L X hd hL hX
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  let t : Real := X / (d : Real)
  have ht : 0 < t := div_pos hX hdR
  have hmu : norm (ArithmeticFunction.moebius d : Complex) <= 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hkEq : k = (k - 1) + 1 := by omega
  have hpow : t ^ k = t ^ (k - 1) * t := by
    calc
      _ = t ^ ((k - 1) + 1) := congrArg (fun j : Nat => t ^ j) hkEq
      _ = _ := pow_succ _ _
  have hinv : (d : Real) / X = 1 / t := by
    dsimp only [t]
    field_simp
  have hinvpow : (1 / t) ^ (k - 1) = 1 / t ^ (k - 1) := by
    rw [div_pow, one_pow]
  calc
    _ = norm (ArithmeticFunction.moebius d : Complex) * t *
        norm (frequencyTail L (FourierTransform.fourier f) t) := by
      simp only [t, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hX hdR)]
    _ <= 1 * t * (C / (t ^ k * (L : Real) ^ (k - 1))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hmu ht.le) (hc L t hL ht)
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [one_mul, hinv, hpow, hinvpow]
      field_simp [ne_of_gt ht] <;> ring

theorem middleTail_norm_bound (f : SchwartzMap Real Complex)
    (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q L : Nat) (X Y Z : Real), 0 < q -> 1 <= L -> 0 < X -> 0 < Z ->
      norm (middleTail q X Y Z L f) <=
      C * Z ^ k / (X ^ (k - 1) * (L : Real) ^ (k - 1)) := by
  choose C hC hc using middleTail_row_bound f k hk
  refine Exists.intro C (And.intro hC ?_)
  intro q L X Y Z hq hL hX hZ
  have hrow (d : Nat) (hd : Membership.mem (middleDivisors q Y Z) d) :
      norm ((ArithmeticFunction.moebius d : Complex) *
        ((X / (d : Real) : Real) : Complex) *
        frequencyTail L (FourierTransform.fourier f) (X / (d : Real))) <=
      C * (Z / X) ^ (k - 1) / (L : Real) ^ (k - 1) := by
    have h := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h.1).1 hq
    have hquot : (d : Real) / X <= Z / X :=
      div_le_div_of_nonneg_right h.2.2 hX.le
    have hp : forall j : Nat, ((d : Real) / X) ^ j <= (Z / X) ^ j := by
      intro j
      induction j with
      | zero => simp only [pow_zero, le_refl]
      | succ j hj =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul hj hquot (by positivity) (by positivity)
    exact (hc d L X hdpos hL hX).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hp (k - 1)) hC.le) (by positivity))
  have hkEq : k = (k - 1) + 1 := by omega
  have hpow : Z ^ k = Z ^ (k - 1) * Z := by
    calc
      _ = Z ^ ((k - 1) + 1) := congrArg (fun j : Nat => Z ^ j) hkEq
      _ = _ := pow_succ _ _
  calc
    _ <= (middleDivisors q Y Z).sum (fun d =>
        norm ((ArithmeticFunction.moebius d : Complex) *
          ((X / (d : Real) : Real) : Complex) *
          frequencyTail L (FourierTransform.fourier f) (X / (d : Real)))) :=
      norm_sum_le _ _
    _ <= (middleDivisors q Y Z).sum (fun _ =>
        C * (Z / X) ^ (k - 1) / (L : Real) ^ (k - 1)) := by
      apply Finset.sum_le_sum
      exact hrow
    _ = ((middleDivisors q Y Z).card : Real) *
        (C * (Z / X) ^ (k - 1) / (L : Real) ^ (k - 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= Z * (C * (Z / X) ^ (k - 1) / (L : Real) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right (middleDivisors_card q hq Y Z hZ.le) (by positivity)
    _ = _ := by rw [hpow, div_pow]; ring

end PrimeFactorOscillations.CoprimeSchwartzMiddle

