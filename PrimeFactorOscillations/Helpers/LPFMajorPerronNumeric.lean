/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.PerronApproximation
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Main
import Mathlib.NumberTheory.Chebyshev
import PrimeFactorOscillations.Helpers.LPFMajorZetaIntegral

/-!
# Numerical Perron remainder for the actual Chebyshev half-sum

The linear Mangoldt prefix bound gives 12/(c-1) for 1<c<=2. The complete
far, both near, and endpoint packets give coefficients 12 and 51, then 87
on the optimized Perron line. The actual vertical Perron integral differs
from the character Chebyshev half-sum by at most this numerical allowance.
All Dirichlet characters are included; the contour shift is separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_chebyshev_psi_linear_numeric (x : Real) (hx : 0 <= x) :
    Chebyshev.psi x <= 6 * x := by
  have h := Chebyshev.psi_le_const_mul_self hx
  have hLogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
  have hLogFour : Real.log (4 : Real) <= 2 := by
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
    linarith
  nlinarith

theorem lpf_LSeries_norm_of_linear_prefix (a : Nat -> Complex) (K c : Real)
    (hK : 0 <= K) (hc : 1 < c) (hc2 : c <= 2)
    (hPrefix : forall n : Nat,
      Finset.sum (Finset.Icc 1 n) (fun j => norm (a j)) <= K * n) :
    norm (LSeries a (c : Complex)) <= 2 * K / (c - 1) := by
  have hBig : Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => Finset.sum (Finset.Icc 1 n) (fun j => norm (a j)))
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
    apply Asymptotics.IsBigO.of_bound K
    exact Filter.Eventually.of_forall (fun n => by
      simpa only [Real.rpow_one, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg (a j))),
        abs_of_nonneg (show (0 : Real) <= (n : Real) from Nat.cast_nonneg n)] using hPrefix n)
  have hAbel := LSeries_eq_mul_integral' a (r := (1 : Real)) (s := (c : Complex)) (by norm_num)
    (by simpa using hc) hBig
  have hc0 : 0 < c := by linarith
  have hg : MeasureTheory.IntegrableOn (fun t : Real => K * t ^ (-c))
      (Set.Ioi (1 : Real)) MeasureTheory.volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith)
      (by norm_num : (0 : Real) < 1)).const_mul K
  have hIntegral : norm (MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real =>
        Finset.sum (Finset.Icc 1 (Nat.floor t)) a * (t : Complex) ^ (-((c : Complex) + 1)))) <=
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => K * t ^ (-c)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hg
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := Set.mem_Ioi.mp ht
    have ht0 : 0 < t := by linarith
    have hNorm : norm (Finset.sum (Finset.Icc 1 (Nat.floor t)) a) <= K * t := by
      calc
        _ <= Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun j => norm (a j)) :=
          norm_sum_le _ _
        _ <= K * (Nat.floor t : Real) := hPrefix (Nat.floor t)
        _ <= K * t := mul_le_mul_of_nonneg_left (Nat.floor_le ht0.le) hK
    have he : t * t ^ (-(c + 1)) = t ^ (-c) := by
      calc
        _ = t ^ (1 : Real) * t ^ (-(c + 1)) := by rw [Real.rpow_one]
        _ = t ^ ((1 : Real) + -(c + 1)) := (Real.rpow_add ht0 _ _).symm
        _ = _ := by congr 1; ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    calc
      _ <= (K * t) * t ^ (-(c + 1)) :=
        mul_le_mul_of_nonneg_right hNorm (Real.rpow_nonneg ht0.le _)
      _ = _ := by rw [mul_assoc, he]
  have hVal : MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => K * t ^ (-c)) = K / (c - 1) := by
    have hi := integral_Ioi_rpow_of_lt (a := -c) (by linarith)
      (by norm_num : (0 : Real) < 1)
    have he : -c + 1 = -(c - 1) := by ring
    rw [he, Real.one_rpow, neg_div_neg_eq] at hi
    rw [MeasureTheory.integral_const_mul, hi]
    ring
  rw [hVal] at hIntegral
  rw [hAbel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  calc
    _ <= c * (K / (c - 1)) := mul_le_mul_of_nonneg_left hIntegral hc0.le
    _ <= 2 * K / (c - 1) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc2 (div_nonneg hK (sub_pos.mpr hc).le)

theorem lpf_vonMangoldtLSeriesNormSum_numeric (c : Real) (hc : 1 < c) (hc2 : c <= 2) :
    BombieriVinogradov.SiegelWalfisz.vonMangoldtLSeriesNormSum c <= 12 / (c - 1) := by
  let a : Nat -> Complex := fun n => (ArithmeticFunction.vonMangoldt n : Complex)
  have hPrefix : forall n : Nat,
      Finset.sum (Finset.Icc 1 n) (fun j => norm (a j)) <= (6 : Real) * n := by
    intro n
    have hSet : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hPsi := lpf_chebyshev_psi_linear_numeric (n : Real) (Nat.cast_nonneg n)
    have hSum : Finset.sum (Finset.Icc 1 n)
        (fun j => ArithmeticFunction.vonMangoldt j) <= (6 : Real) * n := by
      simpa [Chebyshev.psi, hSet] using hPsi
    simpa only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hSum
  have hNorm := lpf_LSeries_norm_of_linear_prefix a 6 c (by norm_num) hc hc2 hPrefix
  norm_num only [show (2 : Real) * 6 = 12 by norm_num] at hNorm
  rw [BombieriVinogradov.SiegelWalfisz.vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hc,
    <- ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (show 1 < (c : Complex).re by simpa using hc)]
  exact ((le_abs_self _).trans (Complex.abs_re_le_norm (LSeries a (c : Complex)))).trans hNorm

theorem lpf_sourcePerron_majorant_numeric {x : Nat} (hx : 2 < x)
    (c T : Real) (hc : 1 < c) (hc2 : c <= 2) (hT : 0 < T) :
    tsum (BombieriVinogradov.SiegelWalfisz.sourcePerronErrorMajorantTerm x c T) <=
      12 * ((x : Real) ^ c / (T * (c - 1))) +
        51 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
  have hx0 : 0 < x := by omega
  have hRaw := BombieriVinogradov.SiegelWalfisz.tsum_sourcePerronErrorMajorantTerm_le_ranges
    hx0 hc (by linarith : c <= 3) hT
  have hVM := lpf_vonMangoldtLSeriesNormSum_numeric c hc hc2
  have hHarm := BombieriVinogradov.SiegelWalfisz.harmonic_le_three_log_two_mul hx0
  have hEnd := BombieriVinogradov.SiegelWalfisz.endpointPerronBoundValue_le_logSquared
    hx (by linarith : 0 <= c) (by linarith : c <= 3) hT
  have hX : 0 < (x : Real) := by exact_mod_cast hx0
  have hX3 : (3 : Real) <= x := by exact_mod_cast (show 3 <= x by omega)
  have hLog : 0 <= Real.log (2 * (x : Real)) :=
    Real.log_nonneg (by linarith)
  have hFar := mul_le_mul_of_nonneg_left hVM
    (show 0 <= (x : Real) ^ c / T by positivity)
  have hNear := mul_le_mul_of_nonneg_left hHarm
    (show 0 <= 8 * (x : Real) * Real.log (2 * (x : Real)) / T by positivity)
  calc
    _ <= (x : Real) ^ c / T * (12 / (c - 1)) +
        2 * (8 * (x : Real) * Real.log (2 * (x : Real)) / T *
          (3 * Real.log (2 * (x : Real)))) +
        3 * (x : Real) * Real.log (2 * (x : Real)) ^ 2 / T := by
      linarith only [hRaw, hFar, hNear, hEnd]
    _ = _ := by
      field_simp [ne_of_gt hT, ne_of_gt (sub_pos.mpr hc)]
      ring

theorem lpf_optimized_sourcePerron_majorant_numeric {x : Nat} (hx : 2 < x)
    (T : Real) (hT : 0 < T) :
    tsum (BombieriVinogradov.SiegelWalfisz.sourcePerronErrorMajorantTerm x
      (BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x) T) <=
      87 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
  have hc := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_gt_one hx
  have hc2 := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_le_two hx
  have hMain := lpf_sourcePerron_majorant_numeric hx _ T hc hc2 hT
  have hScale := BombieriVinogradov.SiegelWalfisz.optimizedPerronScale_le hx hT
  linarith only [hMain, hScale]

theorem lpf_Perron_approx_numeric {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {x : Nat} (hx : 2 < x)
    (T : Real) (hT : 0 < T) :
    norm (BombieriVinogradov.SiegelWalfisz.explicitFormulaVerticalIntegral chi x
      (BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x) T -
        BombieriVinogradov.SiegelWalfisz.characterChebyshevHalfSum x chi) <=
      87 * ((x : Real) * Real.log (2 * (x : Real)) ^ 2 / T) := by
  have hc := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_gt_one hx
  exact (BombieriVinogradov.SiegelWalfisz.norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source
    chi (show 0 < x by omega) hc hT).trans
      (lpf_optimized_sourcePerron_majorant_numeric hx T hT)

end PrimeFactorOscillations.QRH
