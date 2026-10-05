/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.ScalarDerivative
import PrimeFactorOscillations.Mathlib.Data.Nat.Factorial.LinearError

/-!
# Falling-factorial approximation of a weighted series

A summable fourth absolute moment controls the second-order error uniformly
in the positive rank. The complete series tail beyond the rank is retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- A summable second absolute moment controls the complete first-order
error, including every term beyond the finite falling-factorial support. -/
theorem descFactorial_coefficient_value_error (r : Nat) (hr : 0 < r)
    (a : Nat -> Real) (h0 : Summable a)
    (h2 : Summable (fun j : Nat => (j : Real) ^ 2 * abs (a j))) :
    abs ((Finset.range (r + 1)).sum
        (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j)) -
      tsum a) <= (tsum (fun j : Nat => (j : Real) ^ 2 * abs (a j))) / (2 * r) := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hden : (0 : Real) < 2 * r := by positivity
  have hkernel (j : Nat) :
      abs ((r.descFactorial j : Real) / (r : Real) ^ j - 1) <=
        (j : Real) ^ 2 / (2 * r) := by
    have hlin := descFactorial_normalized_linear_error_bounds r j hr
    have hle : (r.descFactorial j : Real) / (r : Real) ^ j <= 1 := by
      apply (div_le_one (pow_pos hrR j)).mpr
      exact_mod_cast descFactorial_le_pow r j
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have hmajor : (j : Real) * (j - 1) / (2 * r) <=
        (j : Real) ^ 2 / (2 * r) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [show (0 : Real) <= j from Nat.cast_nonneg j]
    linarith only [hlin.1, hmajor]
  have hmajor (j : Nat) :
      norm (a j * ((r.descFactorial j : Real) / (r : Real) ^ j - 1)) <=
        ((j : Real) ^ 2 * abs (a j)) / (2 * r) := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      abs (a j) * abs ((r.descFactorial j : Real) / (r : Real) ^ j - 1) <=
          abs (a j) * ((j : Real) ^ 2 / (2 * r)) :=
        mul_le_mul_of_nonneg_left (hkernel j) (abs_nonneg (a j))
      _ = ((j : Real) ^ 2 * abs (a j)) / (2 * r) := by ring
  have hfinite : HasSum
      (fun j : Nat => a j * ((r.descFactorial j : Real) / (r : Real) ^ j))
      ((Finset.range (r + 1)).sum
        (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hle : r + 1 <= j :=
      Nat.le_of_not_lt (fun h => hj (Finset.mem_range.mpr h))
    rw [descFactorial_of_lt ((Nat.lt_succ_self r).trans_le hle),
      Nat.cast_zero, zero_div, mul_zero]
  have htotal : HasSum
      (fun j : Nat => a j * ((r.descFactorial j : Real) / (r : Real) ^ j - 1))
      ((Finset.range (r + 1)).sum
        (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j)) - tsum a) := by
    convert hfinite.sub h0.hasSum using 1
    ext j
    ring
  have hbound := tsum_of_norm_bounded
    (h2.hasSum.div_const (2 * (r : Real))) hmajor
  simpa only [Real.norm_eq_abs, htotal.tsum_eq] using hbound

/-- The universal finite kernel gives an absolutely controlled infinite
weighted error. The fourth moment is the actual remainder majorant. -/
theorem descFactorial_weighted_tsum_error (r : Nat) (hr : 0 < r)
    (a : Nat -> Real)
    (h4 : Summable (fun j : Nat => (j : Real) ^ 4 * abs (a j))) :
    abs (tsum (fun j : Nat => a j *
      ((r.descFactorial j : Real) / (r : Real) ^ j - 1 +
        (j : Real) * (j - 1) / (2 * r)))) <=
      (tsum (fun j : Nat => (j : Real) ^ 4 * abs (a j))) / (r : Real) ^ 2 := by
  have hbound : forall j : Nat,
      norm (a j * ((r.descFactorial j : Real) / (r : Real) ^ j - 1 +
        (j : Real) * (j - 1) / (2 * r))) <=
        ((j : Real) ^ 4 * abs (a j)) / (r : Real) ^ 2 := by
    intro j
    have hkernel := descFactorial_normalized_linear_error_bounds r j hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel.1]
    calc
      abs (a j) * ((r.descFactorial j : Real) / (r : Real) ^ j - 1 +
          (j : Real) * (j - 1) / (2 * r)) <=
          abs (a j) * ((j : Real) ^ 4 / (r : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left hkernel.2 (abs_nonneg (a j))
      _ = ((j : Real) ^ 4 * abs (a j)) / (r : Real) ^ 2 := by ring
  simpa only [Real.norm_eq_abs] using
    tsum_of_norm_bounded (h4.hasSum.div_const ((r : Real) ^ 2)) hbound

/-- The normalized finite coefficient differs from its full-series linear
approximation by the fourth-moment remainder, uniformly in the rank. -/
theorem descFactorial_coefficient_linear_error (r : Nat) (hr : 0 < r)
    (a : Nat -> Real) (h0 : Summable a)
    (h2 : Summable (fun j : Nat => a j * ((j : Real) * (j - 1))))
    (h4 : Summable (fun j : Nat => (j : Real) ^ 4 * abs (a j))) :
    abs ((Finset.range (r + 1)).sum
        (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j)) -
      tsum a + (tsum (fun j : Nat => a j * ((j : Real) * (j - 1)))) / (2 * r)) <=
      (tsum (fun j : Nat => (j : Real) ^ 4 * abs (a j))) / (r : Real) ^ 2 := by
  have hfinite : HasSum
      (fun j : Nat => a j * ((r.descFactorial j : Real) / (r : Real) ^ j))
      ((Finset.range (r + 1)).sum
        (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hle : r + 1 <= j := Nat.le_of_not_lt (fun h => hj (Finset.mem_range.mpr h))
    have hlt : r < j := (Nat.lt_succ_self r).trans_le hle
    rw [descFactorial_of_lt hlt, Nat.cast_zero, zero_div, mul_zero]
  have htotal : HasSum
      (fun j : Nat => a j *
        ((r.descFactorial j : Real) / (r : Real) ^ j - 1 +
          (j : Real) * (j - 1) / (2 * r)))
      ((Finset.range (r + 1)).sum
          (fun j => a j * ((r.descFactorial j : Real) / (r : Real) ^ j)) -
        tsum a + (tsum (fun j : Nat => a j * ((j : Real) * (j - 1)))) / (2 * r)) := by
    convert (hfinite.sub h0.hasSum).add (h2.hasSum.div_const (2 * (r : Real))) using 1
    ext j
    ring
  have hbound := descFactorial_weighted_tsum_error r hr a h4
  rw [htotal.tsum_eq] at hbound
  exact hbound

end Nat

namespace FormalMultilinearSeries

/-- Polynomially weighted scalar coefficients are summable strictly inside
the convergence radius. This supplies every fixed moment on a compact disk. -/
theorem summable_nat_pow_mul_abs_of_lt_radius
    (c : Nat -> Real) (b : NNReal)
    (hb : (b : ENNReal) < (ofScalars Real c).radius) (k : Nat) :
    Summable (fun j : Nat => (j : Real) ^ k * abs (c j) * (b : Real) ^ j) := by
  have hd := (ofScalars Real c).norm_mul_pow_le_mul_pow_of_lt_radius hb
  choose a ha C hC hdom using hd
  have haNorm : norm a < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos ha.1]
    exact ha.2
  have hs := (summable_pow_mul_geometric_of_norm_lt_one k haNorm).mul_left C
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg j) k)
      (abs_nonneg (c j))) (pow_nonneg b.coe_nonneg j)) _ hs
  intro j
  have hj := hdom j
  simp only [ofScalars_norm, Real.norm_eq_abs] at hj
  calc
    (j : Real) ^ k * abs (c j) * (b : Real) ^ j =
        (j : Real) ^ k * (abs (c j) * (b : Real) ^ j) := by ring
    _ <= (j : Real) ^ k * (C * a ^ j) :=
      mul_le_mul_of_nonneg_left hj (pow_nonneg (Nat.cast_nonneg j) k)
    _ = C * ((j : Real) ^ k * a ^ j) := by ring

end FormalMultilinearSeries

namespace Nat

/-- A single constant controls every positive rank and every nonnegative
parameter in a compact interval strictly inside the scalar-series radius. -/
theorem descFactorial_coefficient_uniform_error_of_radius
    (c : Nat -> Real) (b : NNReal)
    (hb : (b : ENNReal) < (FormalMultilinearSeries.ofScalars Real c).radius) :
    exists C : Real, 0 <= C /\
      forall (r : Nat), 0 < r -> forall (t : NNReal), t <= b ->
        abs ((Finset.range (r + 1)).sum
          (fun j => c j * (t : Real) ^ j *
            ((r.descFactorial j : Real) / (r : Real) ^ j)) -
          tsum (fun j => c j * (t : Real) ^ j) +
          (tsum (fun j : Nat => c j * (t : Real) ^ j *
            ((j : Real) * (j - 1)))) / (2 * r)) <= C / (r : Real) ^ 2 := by
  have hs := FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius c b hb
  refine Exists.intro
    (tsum (fun j : Nat => (j : Real) ^ 4 * abs (c j) * (b : Real) ^ j))
    (And.intro (tsum_nonneg (fun j => by positivity)) ?_)
  intro r hr t ht
  have hpow : forall j : Nat, (t : Real) ^ j <= (b : Real) ^ j := by
    intro j
    have htb : (t : Real) <= (b : Real) := ht
    gcongr
  have hs0 : Summable (fun j : Nat => abs (c j) * (b : Real) ^ j) := by
    simpa only [pow_zero, one_mul] using hs 0
  have h0 : Summable (fun j : Nat => c j * (t : Real) ^ j) := by
    apply Summable.of_norm_bounded hs0
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg t.coe_nonneg j)]
    exact mul_le_mul_of_nonneg_left (hpow j) (abs_nonneg (c j))
  have h2 : Summable (fun j : Nat => c j * (t : Real) ^ j *
      ((j : Real) * (j - 1))) := by
    apply Summable.of_norm_bounded (hs 2)
    intro j
    have hj : abs ((j : Real) * (j - 1)) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.cast_succ, add_sub_cancel_right]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (j : Real)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg t.coe_nonneg j)]
    calc
      abs (c j) * (t : Real) ^ j * abs ((j : Real) * (j - 1)) <=
          abs (c j) * (b : Real) ^ j * (j : Real) ^ 2 := by
        gcongr
      _ = (j : Real) ^ 2 * abs (c j) * (b : Real) ^ j := by ring
  have hmajor : forall j : Nat,
      (j : Real) ^ 4 * abs (c j * (t : Real) ^ j) <=
        (j : Real) ^ 4 * abs (c j) * (b : Real) ^ j := by
    intro j
    rw [abs_mul, abs_of_nonneg (pow_nonneg t.coe_nonneg j)]
    calc
      (j : Real) ^ 4 * (abs (c j) * (t : Real) ^ j) =
          ((j : Real) ^ 4 * abs (c j)) * (t : Real) ^ j := by ring
      _ <= ((j : Real) ^ 4 * abs (c j)) * (b : Real) ^ j :=
        mul_le_mul_of_nonneg_left (hpow j) (by positivity)
  have h4 : Summable (fun j : Nat => (j : Real) ^ 4 *
      abs (c j * (t : Real) ^ j)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hmajor (hs 4)
  have hmain := descFactorial_coefficient_linear_error r hr
    (fun j => c j * (t : Real) ^ j) h0 h2 h4
  exact hmain.trans (div_le_div_of_nonneg_right
    (h4.tsum_le_tsum hmajor (hs 4)) (sq_nonneg (r : Real)))

/-- Uniform approximation by the scalar-series value and its actual second
derivative, with a single constant on the entire compact parameter range. -/
theorem descFactorial_coefficient_uniform_deriv_error
    (c : Nat -> Real) (b : NNReal)
    (hb : (b : ENNReal) < (FormalMultilinearSeries.ofScalars Real c).radius) :
    exists C : Real, 0 <= C /\
      forall (r : Nat), 0 < r -> forall (t : NNReal), t <= b ->
        abs ((Finset.range (r + 1)).sum
          (fun j => c j * (t : Real) ^ j *
            ((r.descFactorial j : Real) / (r : Real) ^ j)) -
          tsum (fun j => c j * (t : Real) ^ j) +
          ((t : Real) ^ 2 * deriv (deriv (fun y : Real =>
            tsum (fun j : Nat => c j * y ^ j))) (t : Real)) / (2 * r)) <=
          C / (r : Real) ^ 2 := by
  choose C hC hbound using descFactorial_coefficient_uniform_error_of_radius c b hb
  refine Exists.intro C (And.intro hC ?_)
  intro r hr t ht
  have htb : (t : ENNReal) <= (b : ENNReal) := by exact_mod_cast ht
  have htRadius : (nnnorm (t : Real) : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real c).radius := by
    simpa using htb.trans_lt hb
  have hmoment := FormalMultilinearSeries.tsum_factorial_secondMoment_eq
    c (t : Real) htRadius
  simpa only [hmoment] using hbound r hr t ht

end Nat
