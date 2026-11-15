/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedNormalizerBound
import PrimeFactorOscillations.Helpers.HamiltonianGaussianFiniteJet

/-! # Integrated finite jets of the actual compensated Gaussian integral

The dominating Gaussian moment is proved integrable. The complete finite
polynomial, its actual normalized Gaussian state and the full compensated
integral are compared with an explicit small-parameter remainder.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def gaussianCoordinateSquarePolynomial (H : Nat) : MvPolynomial Iota Complex :=
  (Finset.sum Finset.univ (fun j => (MvPolynomial.X j) ^ 2)) ^ H

omit [DecidableEq Iota] in
theorem gaussianCoordinateSquarePolynomial_eval (H : Nat) (x : Iota -> Real) :
    MvPolynomial.eval (fun j => (x j : Complex))
        (gaussianCoordinateSquarePolynomial (Iota := Iota) H) =
      (((Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H : Real) : Complex) := by
  unfold gaussianCoordinateSquarePolynomial
  simp only [map_pow, map_sum, MvPolynomial.eval_X]
  push_cast
  rfl

theorem gaussian_damped_square_moment_integrable (H : Nat) :
    MeasureTheory.Integrable
      (fun x : Iota -> Real =>
        (Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H *
          Real.exp (-(3 / 8 : Real) * Finset.sum Finset.univ (fun j => x j ^ 2)))
      gaussianTensorMeasure := by
  have hPrecision : gaussianTiltPrecision (1 / 3 : Complex) = (3 / 8 : Complex) := by
    norm_num [gaussianTiltPrecision]
  have hKernel : gaussianMvTiltKernel (fun _ : Iota => (1 / 3 : Complex))
      (fun _ => 1) (gaussianCoordinateSquarePolynomial (Iota := Iota) H) =
      (fun x : Iota -> Real =>
        (((Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H *
          Real.exp (-(3 / 8 : Real) * Finset.sum Finset.univ (fun j => x j ^ 2)) : Real) :
            Complex)) := by
    funext x
    unfold gaussianMvTiltKernel
    simp only [one_mul, hPrecision, gaussianCoordinateSquarePolynomial_eval]
    have hExp : Finset.prod Finset.univ (fun j =>
        Complex.exp (-(3 / 8 : Complex) * (x j : Complex) ^ 2)) =
        (Real.exp (-(3 / 8 : Real) *
          Finset.sum Finset.univ (fun j => x j ^ 2)) : Complex) := by
      rw [<- Complex.exp_sum, Complex.ofReal_exp]
      congr 1
      push_cast
      rw [Finset.mul_sum]
    rw [hExp]
    push_cast
    rfl
  have hInt := gaussianMvTiltKernel_integrable
    (fun _ : Iota => (1 / 3 : Complex)) (fun _ => 1)
    (fun _ => by norm_num) (gaussianCoordinateSquarePolynomial (Iota := Iota) H)
  rw [hKernel] at hInt
  convert! hInt.re using 1

def gaussianFiniteJetDominatingMoment (H : Nat) : Real :=
  MeasureTheory.integral gaussianTensorMeasure
    (fun x : Iota -> Real =>
      (Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H *
        Real.exp (-(3 / 8 : Real) * Finset.sum Finset.univ (fun j => x j ^ 2)))

omit [DecidableEq Iota] in
theorem gaussianFiniteJetDominatingMoment_nonnegative (H : Nat) :
    0 <= gaussianFiniteJetDominatingMoment (Iota := Iota) H := by
  unfold gaussianFiniteJetDominatingMoment
  exact MeasureTheory.integral_nonneg (fun x =>
    mul_nonneg (pow_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) H)
      (Real.exp_pos _).le)

omit [DecidableEq Iota] in
theorem realStandardGaussianDensity_exp (x : Iota -> Real) :
    realStandardGaussianDensity x =
      Real.exp (-Finset.sum Finset.univ (fun j => x j ^ 2) / 2) := by
  unfold realStandardGaussianDensity
  rw [<- Real.exp_sum, <- Finset.mul_sum]
  congr 1
  ring

def wickFiniteGaussianJetPolynomial (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (H : Nat) : MvPolynomial Iota Complex :=
  realGaussianAffinePolynomial M hM 1 *
    Finset.sum (Finset.range H) (fun j =>
      MvPolynomial.C (1 / (j.factorial : Complex)) *
        (MvPolynomial.C (1 / 2 : Complex) *
          Finset.sum Finset.univ (fun i =>
            gaussianLinearForm (realGaussianEigenRows M hM i) ^ 2)) ^ j)

theorem wickFiniteGaussianJetPolynomial_eval (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex) (x : Iota -> Real) (H : Nat) :
    MvPolynomial.eval (fun j => w j * (x j : Complex))
        (wickFiniteGaussianJetPolynomial M hM H) =
      wickFiniteGaussianJet (realGaussianWeightedVector M hM w x) H := by
  have hLinear : forall i, MvPolynomial.eval (fun j => w j * (x j : Complex))
      (gaussianLinearForm (realGaussianEigenRows M hM i)) =
        realGaussianWeightedVector M hM w x i := by
    intro i
    simp only [gaussianLinearForm, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rfl
  unfold wickFiniteGaussianJetPolynomial
  rw [map_mul, realGaussianAffinePolynomial_eval_weighted]
  unfold wickFiniteGaussianJet
  congr 1
  simp only [map_sum, map_mul, map_pow, MvPolynomial.eval_C, hLinear]
  apply Finset.sum_congr rfl
  intro j hj
  have hQ : (1 / 2 : Complex) *
      Finset.sum Finset.univ (fun i => realGaussianWeightedVector M hM w x i ^ 2) =
      Finset.sum Finset.univ (fun i => realGaussianWeightedVector M hM w x i ^ 2) / 2 := by
    ring
  rw [hQ]
  ring

theorem wickFiniteGaussianJetPolynomial_kernel (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (t : Real) (H : Nat) (x : Iota -> Real) :
    standardGaussianPolynomialKernel
      (fun j => (t : Complex) * realGaussianEigenVariances M hM j /
        (1 + (t : Complex) * realGaussianEigenVariances M hM j))
      (wickFiniteGaussianJetPolynomial M hM H) x =
      wickFiniteGaussianJet
          (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x) H *
        (realStandardGaussianDensity x : Complex) := by
  unfold standardGaussianPolynomialKernel
  rw [gaussianMvTiltKernel_reweight]
  simp only [zero_div, zero_mul, Finset.sum_const_zero, Complex.exp_zero, mul_one]
  exact congrArg (fun a : Complex => a * (realStandardGaussianDensity x : Complex))
    (wickFiniteGaussianJetPolynomial_eval M hM
      (realGaussianQuotientWeights M hM (t : Complex)) x H)

theorem realGaussianCompensatedAverage_finiteJet_bound [Nonempty Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (rho t : Real) (H : Nat)
    (hNorm : norm M <= rho) (ht : 0 <= t) (hSmall : t * rho <= 1 / 16)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0) :
    norm (realGaussianCompensatedAverage M hM (t : Complex) -
      gaussianPolynomialState
        (fun j => (t : Complex) * realGaussianEigenVariances M hM j /
          (1 + (t : Complex) * realGaussianEigenVariances M hM j))
        (wickFiniteGaussianJetPolynomial M hM H)) <=
      t ^ H * (rho ^ H * gaussianFiniteJetDominatingMoment (Iota := Iota) H /
        realStandardGaussianNormalizer ^ Fintype.card Iota) := by
  let v := fun j => (t : Complex) * realGaussianEigenVariances M hM j /
    (1 + (t : Complex) * realGaussianEigenVariances M hM j)
  let p := wickFiniteGaussianJetPolynomial M hM H
  let g := fun x : Iota -> Real =>
    (Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H *
      Real.exp (-(3 / 8 : Real) * Finset.sum Finset.univ (fun j => x j ^ 2))
  have hDisk : forall j, norm ((t : Complex) * realGaussianEigenVariances M hM j) < 1 := by
    intro j
    have hEigen := le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hNorm
    have h := mul_le_mul_of_nonneg_left hEigen ht
    simp only [norm_mul, realGaussianEigenVariances, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht]
    linarith only [h, hSmall]
  have hComp := realGaussianCompensatedKernel_integrable M hM (t : Complex) hCol hDisk
  have hJet := standardGaussianPolynomialKernel_integrable v p
  have hDamped : MeasureTheory.Integrable g gaussianTensorMeasure :=
    gaussian_damped_square_moment_integrable H
  have hPoint : forall x,
      norm (realGaussianCompensatedKernel M hM (t : Complex) x -
        standardGaussianPolynomialKernel v p x) <= (t ^ H * rho ^ H) * g x := by
    intro x
    dsimp only [v, p]
    rw [wickFiniteGaussianJetPolynomial_kernel, realGaussianCompensatedKernel,
      <- sub_mul, norm_mul,
      Complex.norm_of_nonneg (realStandardGaussianDensity_nonnegative x),
      realStandardGaussianDensity_exp]
    have h := realGaussianQuotientFiniteJet_density_bound M hM rho t H x
      hNorm ht hSmall hCol
    calc
      _ = Real.exp (-Finset.sum Finset.univ (fun j => x j ^ 2) / 2) *
          norm (Finset.prod Finset.univ (fun i => wickVertexFunction
              (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x i)) -
            wickFiniteGaussianJet
              (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x) H) :=
        mul_comm _ _
      _ <= _ := h
      _ = _ := by dsimp only [g]; ring
  have hIntegral :
      norm (MeasureTheory.integral gaussianTensorMeasure
          (realGaussianCompensatedKernel M hM (t : Complex)) -
        MeasureTheory.integral gaussianTensorMeasure (standardGaussianPolynomialKernel v p)) <=
      (t ^ H * rho ^ H) * gaussianFiniteJetDominatingMoment (Iota := Iota) H := by
    rw [<- MeasureTheory.integral_sub hComp hJet]
    calc
      _ <= MeasureTheory.integral gaussianTensorMeasure (fun x =>
          norm (realGaussianCompensatedKernel M hM (t : Complex) x -
            standardGaussianPolynomialKernel v p x)) :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ <= MeasureTheory.integral gaussianTensorMeasure (fun x => (t ^ H * rho ^ H) * g x) :=
        MeasureTheory.integral_mono (hComp.sub hJet).norm (hDamped.const_mul _) hPoint
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        rfl
  have hState : gaussianPolynomialState v p =
      MeasureTheory.integral gaussianTensorMeasure (standardGaussianPolynomialKernel v p) /
        ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex) := by
    have h := standardGaussianPolynomial_normalized v p
    rw [standardGaussianTensor_normalizer_real] at h
    exact h.symm
  have hZ : 0 < realStandardGaussianNormalizer ^ Fintype.card Iota :=
    pow_pos realStandardGaussianNormalizer_positive _
  change norm (realGaussianCompensatedAverage M hM (t : Complex) -
    gaussianPolynomialState v p) <= _
  rw [realGaussianCompensatedAverage, hState, <- sub_div, norm_div,
    Complex.norm_of_nonneg hZ.le]
  calc
    _ <= ((t ^ H * rho ^ H) * gaussianFiniteJetDominatingMoment (Iota := Iota) H) /
        realStandardGaussianNormalizer ^ Fintype.card Iota :=
      div_le_div_of_nonneg_right hIntegral hZ.le
    _ = _ := by ring

theorem stochastic_compensated_finiteJet_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho t : Real) (H : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho)
    (ht : 0 <= t) (hSmall : t * rho <= 1 / 16) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (t : Complex) -
      gaussianPolynomialState
        (fun j => (t : Complex) *
          realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
            (bipartiteLift_hermitian (centeredKernel T q)) j /
          (1 + (t : Complex) *
            realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
              (bipartiteLift_hermitian (centeredKernel T q)) j))
        (wickFiniteGaussianJetPolynomial (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)) H)) <=
      t ^ H * (rho ^ H *
        gaussianFiniteJetDominatingMoment (Iota := Sum (Fin n) (Fin n)) H /
        realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n))) := by
  let : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  have hBalance := centered_bipartite_column_sum_zero T q
    (by simpa only [Fintype.card_fin] using hq) hRow hCol
  have hBlockNorm : norm (bipartiteLift (centeredKernel T q)) <= rho :=
    le_trans (bipartiteLift_l2_norm_le (centeredKernel T q)) hNorm
  have hGap : 0 < 1 - norm (t : Complex) * rho := by
    rw [Complex.norm_of_nonneg ht]
    linarith only [hSmall]
  rw [hamiltonianCompensatedRook_eq_average _ _ hBalance
    (bipartite_eigen_disk _ rho (t : Complex) hNorm hGap)]
  exact realGaussianCompensatedAverage_finiteJet_bound _ _ rho t H
    hBlockNorm ht hSmall hBalance

end PrimeFactorOscillations
