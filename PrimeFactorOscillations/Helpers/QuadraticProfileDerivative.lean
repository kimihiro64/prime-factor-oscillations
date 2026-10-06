/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileSeries
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialPolynomial
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialSeries

/-!
# Uniform derivatives of normalized prime-profile polynomials

The absolute second coefficient moment at a larger radius bounds the actual
first and second derivatives uniformly in the rank, including the zero endpoint.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

theorem exists_profile_normalized_derivative_bounds (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 <= b) :
    exists M : Real, 0 <= M /\
      forall (r : Nat), 0 < r -> forall (t : Real), 0 <= t -> t <= b ->
        abs (deriv (Nat.normalizedDescFactorialPolynomial
          law.realCoefficient r) t) <= M /\
        abs (deriv (deriv (Nat.normalizedDescFactorialPolynomial
          law.realCoefficient r)) t) <= M := by
  let B := b + 1
  have hB : 1 <= B := by dsimp [B]; linarith
  have hB0 : 0 <= B := le_trans zero_le_one hB
  let Bn : NNReal := { val := B, property := hB0 }
  have hrad : (Bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  have hs : Summable (fun j : Nat => (j : Real) ^ 2 *
      abs (law.realCoefficient j) * B ^ j) :=
    FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius
      law.realCoefficient Bn hrad 2
  let M := tsum (fun j : Nat => (j : Real) ^ 2 *
    abs (law.realCoefficient j) * B ^ j)
  have hM : 0 <= M := tsum_nonneg (fun j => by positivity)
  refine Exists.intro M (And.intro hM ?_)
  intro r hr t ht htb
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hkernel : forall j : Nat,
      0 <= (r.descFactorial j : Real) / (r : Real) ^ j /\
        (r.descFactorial j : Real) / (r : Real) ^ j <= 1 := by
    intro j
    refine And.intro (by positivity) ?_
    apply (div_le_one (pow_pos hrR j)).mpr
    exact_mod_cast Nat.descFactorial_le_pow r j
  have hpow : forall j d : Nat, t ^ (j - d) <= B ^ j := by
    intro j d
    have htB : t <= B := by dsimp [B]; linarith
    calc
      t ^ (j - d) <= B ^ (j - d) := by gcongr
      _ <= B ^ j := by
        gcongr
        first | assumption | omega
  have hmajor1 : forall j : Nat,
      norm ((j : Real) * law.realCoefficient j * t ^ (j - 1) *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by
    intro j
    have hj : (j : Real) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.cast_succ]
        nlinarith [sq_nonneg (j : Real), (show (0 : Real) <= j from Nat.cast_nonneg j)]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (pow_nonneg ht (j - 1)), abs_of_nonneg (hkernel j).1]
    calc
      (j : Real) * abs (law.realCoefficient j) * t ^ (j - 1) *
          ((r.descFactorial j : Real) / (r : Real) ^ j) <=
          (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hpow j 1 | exact (hkernel j).2
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by ring
  have hmajor2 : forall j : Nat,
      norm ((j : Real) * ((j - 1 : Nat) : Real) * law.realCoefficient j *
        t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by
    intro j
    have hprev : (((j - 1 : Nat) : Real)) <= j := by
      exact_mod_cast Nat.sub_le j 1
    have hj : (j : Real) * ((j - 1 : Nat) : Real) <= (j : Real) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hprev
        (show (0 : Real) <= j from Nat.cast_nonneg j)]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (show (0 : Real) <= ((j - 1 : Nat) : Real) from Nat.cast_nonneg (j - 1)),
      abs_of_nonneg (pow_nonneg ht (j - 2)), abs_of_nonneg (hkernel j).1]
    calc
      (j : Real) * ((j - 1 : Nat) : Real) * abs (law.realCoefficient j) *
          t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j) <=
          (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hpow j 2 | exact (hkernel j).2
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by ring
  have hsum : (Finset.range (r + 1)).sum (fun j : Nat =>
      (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j) <= M :=
    sum_le_hasSum (Finset.range (r + 1)) (fun j _ => by positivity) hs.hasSum
  constructor
  . rw [Nat.deriv_normalizedDescFactorialPolynomial]
    have hn := (norm_sum_le (Finset.range (r + 1))
      (fun j => (j : Real) * law.realCoefficient j * t ^ (j - 1) *
        ((r.descFactorial j : Real) / (r : Real) ^ j))).trans
      ((Finset.sum_le_sum (fun j _ => hmajor1 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using hn
  . rw [Nat.deriv_deriv_normalizedDescFactorialPolynomial]
    have hn := (norm_sum_le (Finset.range (r + 1))
      (fun j => (j : Real) * ((j - 1 : Nat) : Real) * law.realCoefficient j *
        t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j))).trans
      ((Finset.sum_le_sum (fun j _ => hmajor2 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using hn

end PrimeFactorOscillations.QuadraticPrimeLaw
