/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedNormalizerBound

/-! # Analyticity of the actual compensated Gaussian rook function

The actual scalar integral is identified with its complex-power formula
on the unit disk before the normalizer and rook function are differentiated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open scoped Topology Matrix.Norms.L2Operator

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianTiltMoment_explicit (z : Complex) (hz : norm z < 1) :
    complexGaussianMoment (gaussianTiltPrecision z) 0 =
      (2 * (Real.pi : Complex) * (1 + z)) ^ (1 / 2 : Complex) := by
  rw [complexGaussianMoment_zero _
    (lt_trans (by norm_num) (gaussianTiltPrecision_real_part z hz))]
  have hAdd := gaussian_disk_one_add_ne_zero z hz
  have hBase : (Real.pi : Complex) / gaussianTiltPrecision z =
      2 * (Real.pi : Complex) * (1 + z) := by
    unfold gaussianTiltPrecision
    field_simp
    ring
  rw [hBase]

theorem gaussianTiltMoment_differentiableOn :
    DifferentiableOn Complex
      (fun z : Complex => complexGaussianMoment (gaussianTiltPrecision z) 0)
      {z : Complex | norm z < 1} := by
  have hDiff : DifferentiableOn Complex
      (fun z : Complex => (2 * (Real.pi : Complex) * (1 + z)) ^ (1 / 2 : Complex))
      {z : Complex | norm z < 1} := by
    intro z hz
    change norm z < 1 at hz
    have hRe : 0 < (2 * (Real.pi : Complex) * (1 + z)).re := by
      have hLower : -1 < z.re := by
        have hNeg := Complex.re_le_norm (-z)
        simp only [Complex.neg_re, norm_neg] at hNeg
        linarith
      have hFormula : (2 * (Real.pi : Complex) * (1 + z)).re =
          2 * Real.pi * (1 + z.re) := by
        norm_num [Complex.mul_re, Complex.add_re]
      rw [hFormula]
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith)
    have hSlit : Membership.mem Complex.slitPlane
        (2 * (Real.pi : Complex) * (1 + z)) :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hRe)
    exact (((differentiableAt_const (2 * (Real.pi : Complex))).mul
      ((differentiableAt_const (1 : Complex)).add differentiableAt_id)).cpow_const
        hSlit).differentiableWithinAt
  apply hDiff.congr
  intro z hz
  exact gaussianTiltMoment_explicit z hz

theorem gaussianTiltMoment_differentiableAt (z : Complex) (hz : norm z < 1) :
    DifferentiableAt Complex
      (fun w : Complex => complexGaussianMoment (gaussianTiltPrecision w) 0) z :=
  gaussianTiltMoment_differentiableOn.differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds hz)

omit [DecidableEq Iota] in
theorem gaussianTensorTiltNormalizer_differentiableAt (z : Iota -> Complex)
    (s : Complex) (hDisk : forall j, norm (s * z j) < 1) :
    DifferentiableAt Complex
      (fun t : Complex => gaussianTensorTiltNormalizer (fun j => t * z j)) s := by
  change DifferentiableAt Complex
    (fun t : Complex => Finset.prod Finset.univ
      (fun j => complexGaussianMoment (gaussianTiltPrecision (t * z j)) 0)) s
  apply DifferentiableAt.fun_finsetProd
    (f := fun j (t : Complex) => complexGaussianMoment (gaussianTiltPrecision (t * z j)) 0)
  intro j hj
  have hMul : DifferentiableAt Complex (fun t : Complex => t * z j) s :=
    differentiableAt_id.mul_const (z j)
  have hMoment := gaussianTiltMoment_differentiableAt (s * z j) (hDisk j)
  have hComp := hMoment.comp s hMul
  exact hComp

theorem gaussianTensorTiltNormalizer_analyticOnNhd (z : Iota -> Complex) :
    AnalyticOnNhd Complex
      (fun t : Complex => gaussianTensorTiltNormalizer (fun j => t * z j))
      {t : Complex | forall j, norm (t * z j) < 1} := by
  have hOpen : IsOpen {t : Complex | forall j, norm (t * z j) < 1} := by
    have hSet : {t : Complex | forall j, norm (t * z j) < 1} =
        Set.iInter (fun j : Iota => {t : Complex | norm (t * z j) < 1}) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hSet]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_id.mul continuous_const).norm continuous_const
  apply DifferentiableOn.analyticOnNhd _ hOpen
  intro s hs
  exact (gaussianTensorTiltNormalizer_differentiableAt z s hs).differentiableWithinAt

theorem hamiltonianComplexRookPolynomial_differentiable
    (B : Matrix Iota Iota Real) :
    Differentiable Complex (hamiltonianComplexRookPolynomial B) := by
  intro s
  unfold hamiltonianComplexRookPolynomial
  exact (HasDerivAt.fun_sum (fun sigma _ =>
    HasDerivAt.fun_sum (fun S _ =>
      (hasDerivAt_pow S.card s).const_mul
        (Finset.prod S (fun i => (B (sigma i) i : Complex)) /
          (((Fintype.card Iota - S.card).factorial : Nat) : Complex))))).differentiableAt

theorem hamiltonianCompensatedRook_differentiableAt {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Complex)
    (hDisk : forall j, norm (s * realGaussianEigenVariances (bipartiteLift B)
      (bipartiteLift_hermitian B) j) < 1) :
    DifferentiableAt Complex (hamiltonianCompensatedRook B) s := by
  unfold hamiltonianCompensatedRook
  exact (hamiltonianComplexRookPolynomial_differentiable B s).mul
    ((gaussianTensorTiltNormalizer_differentiableAt _ s hDisk).div_const _)

theorem hamiltonianCompensatedRook_analyticOnNhd {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (rho : Real) (hNorm : norm B <= rho) :
    AnalyticOnNhd Complex (hamiltonianCompensatedRook B)
      {s : Complex | norm s * rho < 1} := by
  have hOpen : IsOpen {s : Complex | norm s * rho < 1} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  apply DifferentiableOn.analyticOnNhd _ hOpen
  intro s hs
  change norm s * rho < 1 at hs
  apply DifferentiableAt.differentiableWithinAt
  exact hamiltonianCompensatedRook_differentiableAt B s
    (bipartite_eigen_disk B rho s hNorm (by linarith [hs]))

theorem hamiltonianCompensatedRook_hasFPowerSeriesOnBall {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (rho : Real) (R : NNReal)
    (hNorm : norm B <= rho) (hR : 0 < R) (hGap : (R : Real) * rho < 1) :
    HasFPowerSeriesOnBall (hamiltonianCompensatedRook B)
      (cauchyPowerSeries (hamiltonianCompensatedRook B) 0 R) 0 R := by
  have hRho : 0 <= rho := le_trans (norm_nonneg B) hNorm
  apply DifferentiableOn.hasFPowerSeriesOnBall _ hR
  intro s hs
  have hSize : norm s <= (R : Real) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs
  have hDisk : norm s * rho < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hSize hRho) hGap
  exact (hamiltonianCompensatedRook_differentiableAt B s
    (bipartite_eigen_disk B rho s hNorm (by linarith))).differentiableWithinAt

end PrimeFactorOscillations
