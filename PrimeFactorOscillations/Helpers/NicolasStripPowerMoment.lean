/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.XiSummability
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripRemainder

/-!
# Arbitrarily small degree loss for the complete upper-strip zero coefficient

The strip geometry gives the two bounds 2/|rho| and n/|rho|^2.
Their interpolation uses every actual canonical xi zero with multiplicity.
For each fixed 0<delta<=1, the existing inverse-(1+delta) moment gives
one constant uniform in every integer degree n>=2, without assuming RH.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

theorem norm_nicolasZeroCoefficient_le_two_inv_norm
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re <= 1) :
    norm (((n : Complex) / ((n : Complex) - rho)) / rho) <=
      2 * Inv.inv (norm rho) := by
  have hr : 0 < norm rho := norm_pos_iff.mpr hRho
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hbN : (n : Real) / 2 <= norm ((n : Complex) - rho) := by
    have h := Complex.re_le_norm ((n : Complex) - rho)
    simp only [Complex.sub_re, Complex.natCast_re] at h
    linarith only [h, hRe, hnR]
  have hb : 0 < norm ((n : Complex) - rho) := by
    linarith only [hbN, hnR]
  have hN : (n : Real) <= 2 * norm ((n : Complex) - rho) := by
    linarith only [hbN]
  have hScale := mul_le_mul_of_nonneg_right hN
    (show 0 <= Inv.inv (norm ((n : Complex) - rho) * norm rho) by positivity)
  rw [norm_div, norm_div, Complex.norm_natCast]
  convert hScale using 1
  all_goals field_simp [hr.ne', hb.ne']

theorem norm_nicolasZeroCoefficient_le_fractional_degree
    {delta : Real} (hd : 0 < delta) (hdOne : delta <= 1)
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re <= 1) :
    norm (((n : Complex) / ((n : Complex) - rho)) / rho) <=
      2 * (n : Real) ^ delta *
        (Inv.inv (norm rho)) ^ (1 + delta) := by
  let u : Real := Inv.inv (norm rho)
  let t : Real := (n : Real) * u
  have hu : 0 < u := inv_pos.mpr (norm_pos_iff.mpr hRho)
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (by omega : 0 < n)
  have ht : 0 < t := mul_pos hnPos hu
  have hIdentity : 2 * u * t ^ delta =
      2 * (n : Real) ^ delta * u ^ (1 + delta) := by
    dsimp only [t]
    rw [Real.mul_rpow hnPos.le hu.le, Real.rpow_add hu,
      Real.rpow_one]
    ring
  by_cases hLarge : 1 <= t
  case pos =>
    have hPower : 1 <= t ^ delta := Real.one_le_rpow hLarge hd.le
    have hScale := mul_le_mul_of_nonneg_left hPower
      (show 0 <= 2 * u by positivity)
    calc
      _ <= 2 * u := norm_nicolasZeroCoefficient_le_two_inv_norm hn hRho hRe
      _ <= 2 * u * t ^ delta := by simpa only [mul_one] using hScale
      _ = _ := hIdentity
  case neg =>
    have hPower : t <= t ^ delta := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge ht (lt_of_not_ge hLarge).le hdOne
    have hScale := mul_le_mul_of_nonneg_left hPower hu.le
    have hTail := norm_nat_div_sub_div_le_strip_weight hn hRho hRe
    calc
      _ <= (n : Real) * u ^ (2 : Nat) := hTail
      _ = u * t := by dsimp only [t]; ring
      _ <= u * t ^ delta := hScale
      _ <= 2 * u * t ^ delta := by
        nlinarith only [mul_nonneg hu.le (Real.rpow_nonneg ht.le delta)]
      _ = _ := hIdentity

theorem exists_nicolasZeroCoefficient_power_bound
    (delta : Real) (hd : 0 < delta) (hdOne : delta <= 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) :
    Exists fun C : Real => And (0 < C) (forall n : Nat, 2 <= n ->
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
          riemannXiDivisorZeroValue p)) <= C * (n : Real) ^ delta) := by
  let W : RiemannXiDivisorZeroIndex -> Real := fun p =>
    (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (1 + delta)
  have hW : Summable W := summable_riemannXiDivisorZero_norm_inv_rpow (by linarith)
  have hWnonneg (p : RiemannXiDivisorZeroIndex) : 0 <= W p :=
    Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
  have hMass : 0 <= tsum W := tsum_nonneg hWnonneg
  let C : Real := 2 * (tsum W + 1)
  have hC : 0 < C := by dsimp only [C]; linarith only [hMass]
  apply Exists.intro C
  apply And.intro hC
  intro n hn
  have hN : 0 <= (n : Real) ^ delta := Real.rpow_nonneg (Nat.cast_nonneg n) delta
  have hMajor : Summable (fun p => (2 * (n : Real) ^ delta) * W p) :=
    hW.mul_left _
  have hPoint (p : RiemannXiDivisorZeroIndex) :
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p) <= (2 * (n : Real) ^ delta) * W p :=
    norm_nicolasZeroCoefficient_le_fractional_degree hd hdOne hn
      (riemannXiDivisorZeroValue_ne_zero p) (hUpper p)
  have hSummable := hMajor.of_nonneg_of_le (fun p => norm_nonneg _) hPoint
  calc
    _ <= tsum (fun p => (2 * (n : Real) ^ delta) * W p) :=
      hSummable.tsum_le_tsum hPoint hMajor
    _ = (2 * (n : Real) ^ delta) * tsum W := tsum_mul_left
    _ <= C * (n : Real) ^ delta := by
      dsimp only [C]
      nlinarith only [hN]

end PrimeFactorOscillations
