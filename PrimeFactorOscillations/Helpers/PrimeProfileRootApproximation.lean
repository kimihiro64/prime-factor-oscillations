/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileDerivative

/-!
# Uniform value and derivative approximation for the prime profile

The same normalized factorial polynomial approximates the actual entire
profile and its real derivative at order inverse rank on a compact interval.
The complete tails and the zero endpoint are included.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_primeProfile_normalized_value_deriv_errors
    (b : Real) (hb : 0 <= b) :
    exists C D : Real, 0 <= C /\ 0 <= D /\
      forall r : Nat, 0 < r -> forall t : Real, 0 <= t -> t <= b ->
        abs (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t -
          (primeProfile (t : Complex)).re) <= C / (r : Real) /\
        abs (deriv (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r) t -
          deriv (fun x : Real => (primeProfile (x : Complex)).re) t) <= D / (r : Real) := by
  let B := b + 1
  have hB : 1 <= B := by dsimp [B]; linarith
  have hB0 : 0 <= B := zero_le_one.trans hB
  let Bn : NNReal := { val := B, property := hB0 }
  have hrad : (Bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real primeProfileRealCoefficient).radius := by
    simp only [primeProfileRealCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  let W := fun (k j : Nat) =>
    (j : Real) ^ k * abs (primeProfileRealCoefficient j) * B ^ j
  have hs (k : Nat) : Summable (W k) :=
    FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius
      primeProfileRealCoefficient Bn hrad k
  have hJ (k : Nat) : 0 <= tsum (W k) := tsum_nonneg (fun j => by positivity)
  refine Exists.intro (tsum (W 2) / 2) (Exists.intro (tsum (W 3) / 2)
    (And.intro (div_nonneg (hJ 2) (by norm_num))
      (And.intro (div_nonneg (hJ 3) (by norm_num)) ?_)))
  intro r hr t ht htb
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hden : (0 : Real) <= 2 * r := by positivity
  have hpow (j d : Nat) : t ^ (j - d) <= B ^ j := by
    have htB : t <= B := by dsimp [B]; linarith
    calc
      t ^ (j - d) <= B ^ (j - d) := by gcongr
      _ <= B ^ j := by gcongr; omega
  let a0 := fun j : Nat => primeProfileRealCoefficient j * t ^ j
  let a1 := fun j : Nat => (j : Real) * primeProfileRealCoefficient j * t ^ (j - 1)
  have h0 : Summable a0 := (hasSum_primeProfileRealCoefficient t).summable
  have hmajor0 (j : Nat) : (j : Real) ^ 2 * abs (a0 j) <= W 2 j := by
    dsimp [a0, W]
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht j)]
    have hp : t ^ j <= B ^ j := by simpa only [Nat.sub_zero] using hpow j 0
    calc
      (j : Real) ^ 2 * (abs (primeProfileRealCoefficient j) * t ^ j) =
          ((j : Real) ^ 2 * abs (primeProfileRealCoefficient j)) * t ^ j := by ring
      _ <= ((j : Real) ^ 2 * abs (primeProfileRealCoefficient j)) * B ^ j :=
        mul_le_mul_of_nonneg_left hp (by positivity)
  have h20 : Summable (fun j : Nat => (j : Real) ^ 2 * abs (a0 j)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hmajor0 (hs 2)
  have hmajor1 (j : Nat) : abs (a1 j) <= W 1 j := by
    dsimp [a1, W]
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg j),
      abs_of_nonneg (pow_nonneg ht (j - 1)), pow_one]
    exact mul_le_mul_of_nonneg_left (hpow j 1) (by positivity)
  have h1 : Summable a1 := by
    apply Summable.of_norm_bounded (hs 1)
    intro j
    simpa only [Real.norm_eq_abs] using hmajor1 j
  have hmajor21 (j : Nat) : (j : Real) ^ 2 * abs (a1 j) <= W 3 j := by
    calc
      (j : Real) ^ 2 * abs (a1 j) <= (j : Real) ^ 2 * W 1 j :=
        mul_le_mul_of_nonneg_left (hmajor1 j) (sq_nonneg _)
      _ = W 3 j := by dsimp [W]; ring
  have h21 : Summable (fun j : Nat => (j : Real) ^ 2 * abs (a1 j)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hmajor21 (hs 3)
  have hfunction : (fun x : Real => (primeProfile (x : Complex)).re) =
      (fun x : Real => tsum (fun j : Nat => primeProfileRealCoefficient j * x ^ j)) := by
    funext x
    exact (hasSum_primeProfileRealCoefficient x).tsum_eq.symm
  have hderiv : deriv (fun x : Real => (primeProfile (x : Complex)).re) t =
      tsum (fun j : Nat => ((j : Real) + 1) * primeProfileRealCoefficient (j + 1) * t ^ j) := by
    rw [hfunction]
    apply (FormalMultilinearSeries.hasDerivAt_scalarSeries primeProfileRealCoefficient t _).deriv
    simp only [primeProfileRealCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  have hshift : Summable (fun j : Nat => a1 (j + 1)) := by
    apply h1.comp_injective
    intro j k heq
    exact Nat.add_right_cancel heq
  have htail := hshift.hasSum.sum_range_add
  have hhead : (Finset.range 1).sum a1 = 0 := by simp [a1]
  rw [hhead, zero_add] at htail
  have ha1 : tsum a1 = deriv (fun x : Real => (primeProfile (x : Complex)).re) t := by
    rw [htail.tsum_eq, hderiv]
    apply tsum_congr
    intro j
    simp only [a1, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  have hv := (Nat.descFactorial_coefficient_value_error r hr a0 h0 h20).trans
    (div_le_div_of_nonneg_right (h20.tsum_le_tsum hmajor0 (hs 2)) hden)
  have hd := (Nat.descFactorial_coefficient_value_error r hr a1 h1 h21).trans
    (div_le_div_of_nonneg_right (h21.tsum_le_tsum hmajor21 (hs 3)) hden)
  have ha0 : tsum a0 = (primeProfile (t : Complex)).re :=
    (hasSum_primeProfileRealCoefficient t).tsum_eq
  rw [ha0] at hv
  rw [ha1] at hd
  constructor
  . simpa only [Nat.normalizedDescFactorialPolynomial, a0, div_div] using hv
  . rw [Nat.deriv_normalizedDescFactorialPolynomial]
    simpa only [a1, div_div] using hd

theorem exists_primeProfile_normalized_secondOrder_error (b : Real) (hb : 0 <= b) :
    exists C : Real, 0 <= C /\
      forall r : Nat, 0 < r -> forall t : Real, 0 <= t -> t <= b ->
        abs (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t -
          (primeProfile (t : Complex)).re +
          (t ^ 2 * deriv (deriv (fun x : Real => (primeProfile (x : Complex)).re)) t) /
            (2 * r)) <= C / (r : Real) ^ 2 := by
  let bn : NNReal := { val := b, property := hb }
  have hrad : (bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real primeProfileRealCoefficient).radius := by
    simp only [primeProfileRealCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  choose C hC hbound using Nat.descFactorial_coefficient_uniform_deriv_error
    primeProfileRealCoefficient bn hrad
  refine Exists.intro C (And.intro hC ?_)
  intro r hr t ht htb
  let tn : NNReal := { val := t, property := ht }
  have h := hbound r hr tn htb
  change abs (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t -
    tsum (fun j : Nat => primeProfileRealCoefficient j * t ^ j) +
    (t ^ 2 * deriv (deriv (fun x : Real =>
      tsum (fun j : Nat => primeProfileRealCoefficient j * x ^ j))) t) /
      (2 * r)) <= C / (r : Real) ^ 2 at h
  have hfunction : (fun x : Real => tsum (fun j : Nat => primeProfileRealCoefficient j * x ^ j)) =
      (fun x : Real => (primeProfile (x : Complex)).re) := by
    funext x
    exact (hasSum_primeProfileRealCoefficient x).tsum_eq
  rw [(hasSum_primeProfileRealCoefficient t).tsum_eq, hfunction] at h
  simpa only [Nat.normalizedDescFactorialPolynomial] using h

end PrimeFactorOscillations
