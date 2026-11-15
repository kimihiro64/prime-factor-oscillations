/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickWindowTail

/-! # Actual signed permanent remainder on a full physical window

The same finite cutoff applies to every real scale in the stated window.
The low Wick polynomial, mixed supports and compensation terms are retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonianCompensatedRook_scaled_hasFPowerSeriesOnBall {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (c : Complex) (rho : Real) (R : NNReal)
    (hNorm : norm B <= rho) (hR : 0 < R)
    (hGap : norm c * (R : Real) * rho < 1) :
    HasFPowerSeriesOnBall (fun z => hamiltonianCompensatedRook B (c * z))
      (cauchyPowerSeries (fun z => hamiltonianCompensatedRook B (c * z)) 0 R) 0 R := by
  have hRho : 0 <= rho := le_trans (norm_nonneg B) hNorm
  apply DifferentiableOn.hasFPowerSeriesOnBall _ hR
  intro z hz
  have hSize : norm z <= (R : Real) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hSmall : norm (c * z) * rho < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSize (norm_nonneg c)) hRho) hGap
  have hOuter := hamiltonianCompensatedRook_differentiableAt B (c * z)
    (bipartite_eigen_disk B rho (c * z) hNorm (by linarith only [hSmall]))
  exact (hOuter.comp z
    ((differentiableAt_const c).mul differentiableAt_id)).differentiableWithinAt

theorem stochastic_compensated_window_lowSeries_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s u V : Real)
    (R : NNReal) (H : Nat)
    (hn : 11 <= n) (hH : 11 <= H) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b)
    (hTheta : b * (1 - delta / 2) < 1)
    (hR : 1 < (R : Real)) (hGap : b * (R : Real) * (1 - delta) < 1)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * (2 * b ^ 2 * a / (1 - b * (1 - delta / 2))) * u <= 1 / 2)
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))) <=
      Real.exp (2 * abs s * (R : Real) /
          (1 - abs s * (R : Real) * (1 - delta)) *
        Real.sqrt ((n : Real) * (a - 1)) +
          abs s ^ 2 * (R : Real) ^ 2 * (a - 1) / 2) *
          (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) +
      (11616 * (1 + 16 * Real.exp 1 *
          (2 * b ^ 2 * a / (1 - b * (1 - delta / 2)))) ^ 11 +
        28 * (16 * Real.exp 1 *
          (2 * b ^ 2 * a / (1 - b * (1 - delta / 2)))) ^ 12 * V ^ 2) / (n : Real) ^ 2 := by
  have hnPos : 0 < n := by omega
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hnPos)
  let B := centeredKernel T q
  let F := fun z => hamiltonianCompensatedRook B ((s : Complex) * z)
  let G := covarianceFormalSeries (HSMul.hSMul s (bipartiteLift B))
  let kappa : Real := 2 * b ^ 2 * a / (1 - b * (1 - delta / 2))
  have hKappa : 0 <= kappa := by
    dsimp only [kappa]
    exact div_nonneg (by positivity) (sub_pos.mpr hTheta).le
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hnPos)
  have hqEq : q = 1 / (n : Real) := by
    apply (eq_div_iff hn0).mpr
    simpa only [mul_comm] using hq
  have hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real) := by
    intro i j
    have h := stochastic_covarianceFormalSeries_mass_bound T q a delta b s H
      (by simpa only [Fintype.card_fin] using hq) ha hRow hCol hNonneg hUpper
      hDelta0 hDelta1 hNorm hb hs hTheta i j
    calc
      _ <= _ := h
      _ = _ := by rw [hqEq]; dsimp only [kappa]; ring
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hDiagrams := wickSeriesTruncatedDiagrams_remainder_bound G H n kappa u V
    hCard hn hH hKappa hu0 hu1 hSmall hEntry hCube hLength
  have hAbsGap : abs s * (R : Real) * (1 - delta) < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs R.property) (sub_nonneg.mpr hDelta1)) hGap
  have hComplexGap : norm (s : Complex) * (R : Real) * (1 - delta) < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hAbsGap
  have hCauchy := stochastic_compensated_scaled_cauchy_tail_bound T q a (1 - delta)
    (s : Complex) R (H + 1) hq ha hRow hCol hNonneg hUpper hNorm hR hComplexGap
  have hR0 : 0 < R := by exact_mod_cast lt_trans (by norm_num : (0 : Real) < 1) hR
  have hSeries := hamiltonianCompensatedRook_scaled_hasFPowerSeriesOnBall B
    (s : Complex) (1 - delta) R hNorm hR0 hComplexGap
  have hCoeff : forall k, hamiltonianCauchyCoefficient F R k =
      PowerSeries.coeff k (wickTaylorSeries F) := by
    intro k
    exact hamiltonianCauchyCoefficient_eq_taylor F R hSeries k
  have hValue : F 1 = hamiltonianCompensatedRook B (s : Complex) := by
    dsimp only [F]
    rw [mul_one]
  change norm (hamiltonianCompensatedRook B (s : Complex) -
    Finset.sum (Finset.range (H + 1)) (hamiltonianCauchyCoefficient F R)) <= _ at hCauchy
  rw [<- hValue] at hCauchy
  simp_rw [hCoeff] at hCauchy
  change norm (F 1 - hamiltonianFiniteSeriesValue H (wickTaylorSeries F)) <= _ at hCauchy
  rw [stochastic_compensated_scaled_finiteSeriesValue T q (1 - delta) s H
    hnPos hq hRow hCol hNorm] at hCauchy
  simp only [Complex.norm_real, Real.norm_eq_abs] at hCauchy
  let S := hamiltonianFiniteSeriesValue H (wickSeriesTruncatedDiagrams G H)
  let L := hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams G)
  change norm (hamiltonianCompensatedRook B (s : Complex) - L) <= _
  rw [<- hValue]
  have hSplit : F 1 - L = (F 1 - S) + (S - L) := by ring
  rw [hSplit]
  have h := le_trans (norm_add_le (F 1 - S) (S - L)) (add_le_add hCauchy hDiagrams)
  simpa only [kappa, mul_pow, mul_assoc] using h


def stochasticLowWickValue {n : Nat} (T : Matrix (Fin n) (Fin n) Real)
    (q s : Real) : Complex :=
  gaussianWickLowValue
    (fun j => (s : Complex) *
        realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)) j /
      (1 + (s : Complex) *
        realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)) j))
    (realGaussianEigenRows (bipartiteLift (centeredKernel T q))
      (bipartiteLift_hermitian (centeredKernel T q)))

theorem stochastic_compensated_fullLow_window_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s u V : Real)
    (R : NNReal) (H : Nat)
    (hn : 11 <= n) (hH : 11 <= H) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b)
    (hR : 1 < (R : Real)) (hTheta : b * (R : Real) * (1 - delta / 2) < 1)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * (2 * b ^ 2 * a / (1 - b * (1 - delta / 2))) * u <= 1 / 2)
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      stochasticLowWickValue T q s) <=
      Real.exp (2 * abs s * (R : Real) /
          (1 - abs s * (R : Real) * (1 - delta)) *
        Real.sqrt ((n : Real) * (a - 1)) +
          abs s ^ 2 * (R : Real) ^ 2 * (a - 1) / 2) *
          (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) +
      (11616 * (1 + 16 * Real.exp 1 *
          (2 * b ^ 2 * a / (1 - b * (1 - delta / 2)))) ^ 11 +
        28 * (16 * Real.exp 1 *
          (2 * b ^ 2 * a / (1 - b * (1 - delta / 2)))) ^ 12 * V ^ 2) / (n : Real) ^ 2 +
      10 * (1 + 16 * Real.exp 1 *
        (2 * (b * (R : Real)) ^ 2 * a /
          (1 - b * (R : Real) * (1 - delta / 2)))) ^ 3 *
        (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) := by
  have hb0 : 0 <= b := le_trans (by norm_num) hb
  have hBase : b <= b * (R : Real) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR.le hb0
  have hTheta0 : 0 <= 1 - delta / 2 := by linarith
  have hThetaBase : b * (1 - delta / 2) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBase hTheta0) hTheta
  have hGap : b * (R : Real) * (1 - delta) < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (show 1 - delta <= 1 - delta / 2 by linarith) (mul_nonneg hb0 R.property)) hTheta
  have hMain := stochastic_compensated_window_lowSeries_remainder T q a delta b s u V R H
    hn hH hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hb hs hThetaBase
    hR hGap hu0 hu1 hSmall hCube hLength
  have hLow := stochastic_lowWick_window_tail T q a delta b s R H
    (by omega) hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hb hs hR hTheta
  let X := hamiltonianCompensatedRook (centeredKernel T q) (s : Complex)
  let L := stochasticLowWickValue T q s
  let P := hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams
    (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))
  change norm (X - P) <= _ at hMain
  change norm (L - P) <= _ at hLow
  rw [norm_sub_rev] at hLow
  change norm (X - L) <= _
  have hSplit : X - L = (X - P) + (P - L) := by ring
  rw [hSplit]
  exact le_trans (norm_add_le _ _) (add_le_add hMain hLow)

end PrimeFactorOscillations
