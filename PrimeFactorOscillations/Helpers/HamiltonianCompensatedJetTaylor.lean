/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAnalyticRayOrder
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedAnalyticTransfer
import PrimeFactorOscillations.Helpers.HamiltonianGaussianFiniteJetIntegral
import PrimeFactorOscillations.Helpers.HamiltonianWickTaylorSeries

/-! # Taylor matching for the actual integrated compensated jet

The normalized Gaussian state is polynomial in arbitrary complex covariance
coordinates. Analyticity and the proved positive-real finite-jet bound identify
the actual compensated rook Taylor coefficients with those of the finite
Gaussian jet. The constant used for this identification may depend on the
dimension; the uniform diagram estimates are applied only after exact matching.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem gaussianWickMonomial_analyticAt (z : Complex -> Complex) (s : Complex)
    (hz : AnalyticAt Complex z s) (n : Nat) :
    AnalyticAt Complex (fun w => gaussianWickMonomial (z w) n) s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact analyticAt_const
    | succ n =>
      cases n with
      | zero => exact analyticAt_const
      | succ n =>
        change AnalyticAt Complex
          (fun w => ((n + 1 : Nat) : Complex) * z w * gaussianWickMonomial (z w) n) s
        exact (analyticAt_const.mul hz).mul (ih n (by omega))

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianMonomialState_analyticAt
    (z : Complex -> Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s) (d : Iota -> Nat) :
    AnalyticAt Complex (fun w => gaussianMonomialState (z w) d) s := by
  unfold gaussianMonomialState
  apply Finset.analyticAt_fun_prod
  intro j hj
  exact gaussianWickMonomial_analyticAt (fun w => z w j) s (hz j) (d j)

theorem gaussianPolynomialState_analyticAt
    (z : Complex -> Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s)
    (p : MvPolynomial Iota Complex) :
    AnalyticAt Complex (fun w => gaussianPolynomialState (z w) p) s := by
  change AnalyticAt Complex
    (fun w => Finset.sum p.support
      (fun d => p.coeff d * gaussianMonomialState (z w) (fun j => d j))) s
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact analyticAt_const.mul (gaussianMonomialState_analyticAt z s hz (fun j => d j))

def realGaussianQuotientPolynomialState (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (p : MvPolynomial Iota Complex) (s : Complex) : Complex :=
  gaussianPolynomialState
    (fun j => s * realGaussianEigenVariances M hM j /
      (1 + s * realGaussianEigenVariances M hM j)) p

theorem realGaussianQuotientPolynomialState_analyticAt_zero
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (p : MvPolynomial Iota Complex) :
    AnalyticAt Complex (realGaussianQuotientPolynomialState M hM p) 0 := by
  unfold realGaussianQuotientPolynomialState
  apply gaussianPolynomialState_analyticAt
  intro j
  exact (analyticAt_id.mul analyticAt_const).div
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)

theorem stochastic_compensated_finiteJet_taylor_match {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (H k : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hk : k < H) :
    PowerSeries.coeff k (wickTaylorSeries
        (hamiltonianCompensatedRook (centeredKernel T q))) =
      PowerSeries.coeff k (wickTaylorSeries
        (realGaussianQuotientPolynomialState (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q))
          (wickFiniteGaussianJetPolynomial (bipartiteLift (centeredKernel T q))
            (bipartiteLift_hermitian (centeredKernel T q)) H))) := by
  let B := centeredKernel T q
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let p := wickFiniteGaussianJetPolynomial M hM H
  let F := hamiltonianCompensatedRook B
  let G := realGaussianQuotientPolynomialState M hM p
  have hRho : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hF : AnalyticAt Complex F 0 :=
    hamiltonianCompensatedRook_analyticOnNhd B rho hNorm 0 (by simp)
  have hG : AnalyticAt Complex G 0 :=
    realGaussianQuotientPolynomialState_analyticAt_zero M hM p
  let C : Real := rho ^ H *
    gaussianFiniteJetDominatingMoment (Iota := Sum (Fin n) (Fin n)) H /
      realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n))
  have hC : 0 <= C := div_nonneg
    (mul_nonneg (pow_nonneg hRho _)
      (gaussianFiniteJetDominatingMoment_nonnegative H))
    (pow_pos realStandardGaussianNormalizer_positive _).le
  let r : Real := 1 / (16 * (rho + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hBound : forall t : Real, 0 < t -> t < r ->
      norm ((F - G) (t : Complex)) <= C * t ^ H := by
    intro t ht htr
    have hDen : Not (16 * (rho + 1) = 0) := ne_of_gt (by positivity)
    have hInv : r * (16 * (rho + 1)) = 1 := by
      dsimp only [r]
      field_simp
    have hMul := mul_lt_mul_of_pos_right htr
      (show 0 < 16 * (rho + 1) by positivity)
    rw [hInv] at hMul
    have hSmall : t * rho <= 1 / 16 := by nlinarith
    have h := stochastic_compensated_finiteJet_bound T q rho t H
      hn hq hRow hCol hNorm ht.le hSmall
    change norm (F (t : Complex) - G (t : Complex)) <= C * t ^ H
    simpa only [F, G, realGaussianQuotientPolynomialState, p, M, hM, B, C, mul_comm]
      using h
  have hDeriv := hamiltonian_derivatives_zero_of_positive_ray (F - G)
    (hF.sub hG) H C r hC hr hBound k hk
  rw [iteratedDeriv_sub hF.contDiffAt hG.contDiffAt] at hDeriv
  have hEqual : iteratedDeriv k F 0 = iteratedDeriv k G 0 := sub_eq_zero.mp hDeriv
  change PowerSeries.coeff k (wickTaylorSeries F) =
    PowerSeries.coeff k (wickTaylorSeries G)
  rw [wickTaylorSeries_coeff, wickTaylorSeries_coeff, hEqual]

end PrimeFactorOscillations
