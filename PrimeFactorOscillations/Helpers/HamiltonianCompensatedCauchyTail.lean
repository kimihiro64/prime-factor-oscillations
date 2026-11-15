/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedAnalyticTransfer

/-! # Cauchy coefficients and the actual compensated rook tail

The actual holomorphic function supplies the convergent Taylor series.
The circle estimate controls its complete omitted tail; no infinite Wick
expansion at parameter one is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Topology Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCauchyCoefficient (f : Complex -> Complex) (R : Real) (k : Nat) : Complex :=
  cauchyPowerSeries f 0 R k (fun _ => 1)

theorem hamiltonianCauchyCoefficient_norm_bound
    (f : Complex -> Complex) (R M : Real) (k : Nat)
    (hR : 0 < R)
    (hCircle : forall z, Membership.mem (Metric.sphere (0 : Complex) R) z ->
      norm (f z) <= M) :
    norm (hamiltonianCauchyCoefficient f R k) <= M * (Inv.inv R) ^ k := by
  unfold hamiltonianCauchyCoefficient
  rw [cauchyPowerSeries_apply]
  have hBound := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z : Complex =>
      (1 / (z - 0)) ^ k * ((Inv.inv (z - 0)) * f z))
    (c := (0 : Complex)) hR.le (C := (Inv.inv R) ^ k * ((Inv.inv R) * M)) (by
      intro z hz
      have hNorm : norm z = R := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, one_div, norm_mul, norm_pow, norm_inv, hNorm]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hCircle z hz) (inv_nonneg.mpr hR.le))
        (pow_nonneg (inv_nonneg.mpr hR.le) k))
  change norm ((Inv.inv (2 * (Real.pi : Complex) * Complex.I)) *
    circleIntegral (fun z : Complex =>
      (1 / (z - 0)) ^ k * ((Inv.inv (z - 0)) * f z)) 0 R) <= _
  calc
    _ <= R * ((Inv.inv R) ^ k * ((Inv.inv R) * M)) := hBound
    _ = M * (Inv.inv R) ^ k := by
      have hR0 : Not (R = 0) := ne_of_gt hR
      field_simp

theorem hamiltonianCauchyTail_of_hasSum
    (f : Complex -> Complex) (R M : Real) (H : Nat)
    (hR : 1 < R)
    (hSeries : HasSum (hamiltonianCauchyCoefficient f R) (f 1))
    (hCircle : forall z, Membership.mem (Metric.sphere (0 : Complex) R) z ->
      norm (f z) <= M) :
    norm (f 1 - Finset.sum (Finset.range H) (hamiltonianCauchyCoefficient f R)) <=
      M * (Inv.inv R) ^ H / (1 - (Inv.inv R)) := by
  have hR0 : 0 < R := lt_trans (by norm_num) hR
  have hInv0 : 0 <= (Inv.inv R) := inv_nonneg.mpr hR0.le
  have hInv1 : (Inv.inv R) < 1 := by
    have hId : Inv.inv R * R = 1 := by field_simp
    by_contra hNot
    have h := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hR0.le
    rw [one_mul, hId] at h
    linarith
  have hInvNorm : norm (Inv.inv R) < 1 := by
    simpa only [Real.norm_of_nonneg hInv0] using hInv1
  have hTail : HasSum
      (fun j : Nat => hamiltonianCauchyCoefficient f R (j + H))
      (f 1 - Finset.sum (Finset.range H) (hamiltonianCauchyCoefficient f R)) :=
    (hasSum_nat_add_iff' H).mpr hSeries
  have hGeo := (hasSum_geometric_of_norm_lt_one hInvNorm).mul_left (M * (Inv.inv R) ^ H)
  have hBound := hTail.norm_le_of_bounded hGeo (fun j => by
    calc
      _ <= M * (Inv.inv R) ^ (j + H) :=
        hamiltonianCauchyCoefficient_norm_bound f R M (j + H) hR0 hCircle
      _ = (M * (Inv.inv R) ^ H) * (Inv.inv R) ^ j := by rw [pow_add]; ring)
  simpa only [div_eq_mul_inv] using hBound

theorem hamiltonianCompensatedRook_cauchy_hasSum {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (rho : Real) (R : NNReal)
    (hNorm : norm B <= rho) (hR : 1 < (R : Real)) (hGap : (R : Real) * rho < 1) :
    HasSum (hamiltonianCauchyCoefficient (hamiltonianCompensatedRook B) R)
      (hamiltonianCompensatedRook B 1) := by
  have hR0 : 0 < R := by exact_mod_cast (lt_trans (by norm_num : (0 : Real) < 1) hR)
  have hOne : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) (1 : Complex) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    simpa only [nnnorm_one] using
      (show (1 : NNReal) < R by exact_mod_cast hR)
  have hSeries := (hamiltonianCompensatedRook_hasFPowerSeriesOnBall B rho R
    hNorm hR0 hGap).hasSum hOne
  change HasSum
    (fun k => cauchyPowerSeries (hamiltonianCompensatedRook B) 0 R k (fun _ => 1))
    (hamiltonianCompensatedRook B 1)
  simpa only [zero_add] using hSeries

theorem stochastic_compensated_cauchy_coefficient_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (R : NNReal) (k : Nat)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho)
    (hR : 0 < (R : Real)) (hGap : (R : Real) * rho < 1) :
    norm (hamiltonianCauchyCoefficient
      (hamiltonianCompensatedRook (centeredKernel T q)) R k) <=
      Real.exp (2 * (R : Real) / (1 - (R : Real) * rho) *
        Real.sqrt ((n : Real) * (a - 1)) + (R : Real) ^ 2 * (a - 1) / 2) *
          (Inv.inv (R : Real)) ^ k := by
  apply hamiltonianCauchyCoefficient_norm_bound _ _ _ _ hR
  intro z hz
  have hSize : norm z = (R : Real) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have h := stochastic_compensated_rook_circle_bound T q a rho z
    hq ha hRow hCol hNonneg hUpper hNorm (by rw [hSize]; linarith)
  simpa only [hSize] using h

theorem stochastic_compensated_cauchy_tail_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (R : NNReal) (H : Nat)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho)
    (hR : 1 < (R : Real)) (hGap : (R : Real) * rho < 1) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) 1 -
      Finset.sum (Finset.range H)
        (hamiltonianCauchyCoefficient
          (hamiltonianCompensatedRook (centeredKernel T q)) R)) <=
      Real.exp (2 * (R : Real) / (1 - (R : Real) * rho) *
        Real.sqrt ((n : Real) * (a - 1)) + (R : Real) ^ 2 * (a - 1) / 2) *
          (Inv.inv (R : Real)) ^ H / (1 - (Inv.inv (R : Real))) := by
  apply hamiltonianCauchyTail_of_hasSum _ _ _ H hR
    (hamiltonianCompensatedRook_cauchy_hasSum _ rho R hNorm hR hGap)
  intro z hz
  have hSize : norm z = (R : Real) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have h := stochastic_compensated_rook_circle_bound T q a rho z
    hq ha hRow hCol hNonneg hUpper hNorm (by rw [hSize]; linarith)
  simpa only [hSize] using h

theorem hamiltonianCompensatedRook_scaled_cauchy_hasSum {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (c : Complex) (rho : Real) (R : NNReal)
    (hNorm : norm B <= rho) (hR : 1 < (R : Real))
    (hGap : norm c * (R : Real) * rho < 1) :
    HasSum
      (hamiltonianCauchyCoefficient (fun z => hamiltonianCompensatedRook B (c * z)) R)
      (hamiltonianCompensatedRook B c) := by
  have hRho : 0 <= rho := le_trans (norm_nonneg B) hNorm
  have hR0 : 0 < R := by exact_mod_cast (lt_trans (by norm_num : (0 : Real) < 1) hR)
  have hDiff : DifferentiableOn Complex
      (fun z => hamiltonianCompensatedRook B (c * z))
      (Metric.closedBall 0 (R : Real)) := by
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
    have hInner : DifferentiableAt Complex (fun w : Complex => c * w) z :=
      (differentiableAt_const c).mul differentiableAt_id
    have hCompose := hOuter.comp z hInner
    exact hCompose.differentiableWithinAt
  have hOne : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) (1 : Complex) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    simpa only [nnnorm_one] using
      (show (1 : NNReal) < R by exact_mod_cast hR)
  have hSeries := (hDiff.hasFPowerSeriesOnBall hR0).hasSum hOne
  change HasSum
    (fun k => cauchyPowerSeries (fun z => hamiltonianCompensatedRook B (c * z)) 0 R k
      (fun _ => 1)) (hamiltonianCompensatedRook B c)
  simpa only [zero_add, mul_one] using hSeries

theorem stochastic_compensated_scaled_cauchy_tail_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (c : Complex) (R : NNReal) (H : Nat)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho)
    (hR : 1 < (R : Real)) (hGap : norm c * (R : Real) * rho < 1) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) c -
      Finset.sum (Finset.range H) (hamiltonianCauchyCoefficient
        (fun z => hamiltonianCompensatedRook (centeredKernel T q) (c * z)) R)) <=
      Real.exp (2 * (norm c * (R : Real)) / (1 - norm c * (R : Real) * rho) *
        Real.sqrt ((n : Real) * (a - 1)) +
          (norm c * (R : Real)) ^ 2 * (a - 1) / 2) *
        (Inv.inv (R : Real)) ^ H / (1 - Inv.inv (R : Real)) := by
  have hSeries := hamiltonianCompensatedRook_scaled_cauchy_hasSum
    (centeredKernel T q) c rho R hNorm hR hGap
  have hCircle : forall z, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) z ->
      norm (hamiltonianCompensatedRook (centeredKernel T q) (c * z)) <=
        Real.exp (2 * (norm c * (R : Real)) / (1 - norm c * (R : Real) * rho) *
          Real.sqrt ((n : Real) * (a - 1)) +
            (norm c * (R : Real)) ^ 2 * (a - 1) / 2) := by
    intro z hz
    have hSize : norm (c * z) = norm c * (R : Real) := by
      rw [norm_mul]
      congr 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have h := stochastic_compensated_rook_circle_bound T q a rho (c * z)
      hq ha hRow hCol hNonneg hUpper hNorm (by rw [hSize]; linarith only [hGap])
    simpa only [hSize] using h
  have h := hamiltonianCauchyTail_of_hasSum
    (fun z => hamiltonianCompensatedRook (centeredKernel T q) (c * z)) R _ H hR
    (by simpa only [mul_one] using hSeries) hCircle
  simpa only [mul_one] using h

end PrimeFactorOscillations
