/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierProduct

/-!
# Uniform Carrier Bounds

Uniform coefficient and normalized derivative bounds for finite canonical profiles.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

open BombieriVinogradov.ComplexAnalysis

def prefixCoefficient (law : PrimeClockLaw) (N j : Nat) : Real :=
  (taylorCoefficient (law.complexPrefix N) 0 j).re

def prefixRatio (law : PrimeClockLaw) (N r : Nat) (u : Real) : Real :=
  Nat.factorialConvolution (prefixCoefficient law N) (r - 1) u /
    Nat.factorialConvolution (prefixCoefficient law N) r u

theorem canonical_prefix_coefficient_bound (law : PrimeClockLaw)
    (hs : law.scale = 1) (he : law.error = 0)
    (R : Real) (hR : 0 < R) (N j : Nat) :
    abs (prefixCoefficient law N j) <= productBound R / R ^ j := by
  apply (Complex.abs_re_le_norm _).trans
  apply norm_taylorCoefficient_le j hR (law.differentiable_complexPrefix N)
  intro z hz
  have hball : Membership.mem (Metric.closedBall (0 : Complex) R) z :=
    Metric.sphere_subset_closedBall hz
  have hzR : norm z <= R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball
  exact (canonical_product_bounds law hs he R hR.le z hzR (primeProfilePrefixSet N)).1

theorem normalized_derivative_uniform_bound (b : Real) (hb : 0 <= b)
    (C : Real) (hC : 0 <= C) :
    exists M : Real, 0 <= M /\ forall c : Nat -> Real,
      (forall j, abs (c j) <= C / (2 * (b + 1)) ^ j) ->
      forall r : Nat, 0 < r -> forall t : Real, 0 <= t -> t <= b ->
        abs (deriv (Nat.normalizedDescFactorialPolynomial c r) t) <= M /\
        abs (deriv (deriv (Nat.normalizedDescFactorialPolynomial c r)) t) <= M := by
  let B := b + 1
  let R := 2 * B
  have hB : 1 <= B := by dsimp [B]; linarith
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hR : 0 < R := by dsimp [R]; positivity
  have hseries : Summable (fun j : Nat => (j : Real) ^ 2 * (1 / 2 : Real) ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  let J := tsum (fun j : Nat => (j : Real) ^ 2 * (1 / 2 : Real) ^ j)
  refine Exists.intro (C * J) (And.intro (mul_nonneg hC (tsum_nonneg (fun j => by positivity))) ?_)
  intro c hc r hr t ht htb
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hk (j : Nat) : 0 <= (r.descFactorial j : Real) / (r : Real) ^ j /\
      (r.descFactorial j : Real) / (r : Real) ^ j <= 1 := by
    refine And.intro (by positivity) ?_
    apply (div_le_one (pow_pos hrR j)).mpr
    exact_mod_cast Nat.descFactorial_le_pow r j
  have hp (j d : Nat) : t ^ (j - d) <= B ^ j := by
    calc
      _ <= B ^ (j - d) := by gcongr; dsimp [B]; linarith
      _ <= B ^ j := by gcongr; omega
  have hm (j : Nat) :
      (j : Real) ^ 2 * abs (c j) * B ^ j <= C * ((j : Real) ^ 2 * (1 / 2 : Real) ^ j) := by
    calc
      _ <= (j : Real) ^ 2 * (C / R ^ j) * B ^ j := by
        gcongr
        exact hc j
      _ = C * ((j : Real) ^ 2 * (B / R) ^ j) := by rw [div_pow]; ring
      _ = _ := by
        have heq : B / R = (1 / 2 : Real) := by dsimp [R]; field_simp
        rw [heq]
  have hsum : (Finset.range (r + 1)).sum
      (fun j => (j : Real) ^ 2 * abs (c j) * B ^ j) <= C * J := by
    apply (Finset.sum_le_sum (fun j _ => hm j)).trans
    simpa only [J, tsum_mul_left] using
      (hseries.mul_left C).sum_le_tsum (Finset.range (r + 1)) (fun j _ => by positivity)
  have hmajor1 (j : Nat) :
      norm ((j : Real) * c j * t ^ (j - 1) *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (c j) * B ^ j := by
    have hj : (j : Real) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j => simp only [Nat.cast_succ]; nlinarith [(show (0 : Real) <= j from Nat.cast_nonneg j)]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (pow_nonneg ht _), abs_of_nonneg (hk j).1]
    calc
      _ <= (j : Real) ^ 2 * abs (c j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hp j 1 | exact (hk j).2
      _ = _ := by ring
  have hmajor2 (j : Nat) :
      norm ((j : Real) * ((j - 1 : Nat) : Real) * c j * t ^ (j - 2) *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (c j) * B ^ j := by
    have hprev : (((j - 1 : Nat) : Real)) <= j := by exact_mod_cast Nat.sub_le j 1
    have hj : (j : Real) * ((j - 1 : Nat) : Real) <= (j : Real) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hprev ((show (0 : Real) <= j from Nat.cast_nonneg j))]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (show (0 : Real) <= (j - 1 : Nat) from Nat.cast_nonneg (j - 1)), abs_of_nonneg (pow_nonneg ht _),
      abs_of_nonneg (hk j).1]
    calc
      _ <= (j : Real) ^ 2 * abs (c j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hp j 2 | exact (hk j).2
      _ = _ := by ring
  constructor
  . rw [Nat.deriv_normalizedDescFactorialPolynomial]
    have h := (norm_sum_le (Finset.range (r + 1)) _).trans
      ((Finset.sum_le_sum (fun j _ => hmajor1 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using h
  . rw [Nat.deriv_deriv_normalizedDescFactorialPolynomial]
    have h := (norm_sum_le (Finset.range (r + 1)) _).trans
      ((Finset.sum_le_sum (fun j _ => hmajor2 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using h

end PrimeFactorOscillations.UniformCarrier
