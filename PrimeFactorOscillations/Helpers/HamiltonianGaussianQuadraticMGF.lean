/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianSpectralRealization

/-! # Actual Gaussian exponential moments with trace dependence

The full quadratic energy is integrated against the standard Gaussian
density. The bound depends on the sum of the coordinate weights, not on
the ambient dimension times their maximum. It controls only the retained
analytic tails, after the signed low-degree terms have been kept.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

def realStandardGaussianNormalizer : Real := Real.sqrt (2 * Real.pi)

theorem realStandardGaussianNormalizer_positive : 0 < realStandardGaussianNormalizer :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)

theorem realStandardGaussianNormalizer_sq :
    realStandardGaussianNormalizer ^ 2 = 2 * Real.pi :=
  Real.sq_sqrt (mul_nonneg (by norm_num) Real.pi_pos.le)

def realQuadraticGaussianIntegral (u : Real) : Real :=
  MeasureTheory.integral MeasureTheory.volume
    (fun x : Real => Real.exp (-((1 - u) / 2) * x ^ 2))

theorem realQuadraticGaussianIntegral_nonnegative (u : Real) :
    0 <= realQuadraticGaussianIntegral u := by
  rw [realQuadraticGaussianIntegral, integral_gaussian]
  exact Real.sqrt_nonneg _

theorem realQuadraticGaussianIntegral_sq (u : Real) (hGap : 0 < 1 - u) :
    realQuadraticGaussianIntegral u ^ 2 = 2 * Real.pi / (1 - u) := by
  have hB : 0 < (1 - u) / 2 := div_pos hGap (by norm_num)
  have hRatio : 0 <= Real.pi / ((1 - u) / 2) := (div_pos Real.pi_pos hB).le
  rw [realQuadraticGaussianIntegral, integral_gaussian, Real.sq_sqrt hRatio]
  field_simp <;> ring

theorem realQuadraticGaussianIntegral_zero :
    realQuadraticGaussianIntegral 0 = realStandardGaussianNormalizer := by
  rw [realQuadraticGaussianIntegral, integral_gaussian, realStandardGaussianNormalizer]
  congr 1
  norm_num <;> ring

theorem realQuadraticGaussianIntegral_bound (u g : Real) (hu : 0 <= u)
    (hGap : 0 < 1 - u) (hg : 0 < g) (hgLe : g <= 1 - u) :
    realQuadraticGaussianIntegral u <=
      realStandardGaussianNormalizer * Real.exp (u / g) := by
  let J := realQuadraticGaussianIntegral u
  let Z := realStandardGaussianNormalizer
  have hJ0 : 0 <= J := realQuadraticGaussianIntegral_nonnegative u
  have hZ0 : 0 < Z := realStandardGaussianNormalizer_positive
  have hJ := realQuadraticGaussianIntegral_sq u hGap
  have hZ := realStandardGaussianNormalizer_sq
  have hIdentity : J ^ 2 * (1 - u) = Z ^ 2 := by
    change realQuadraticGaussianIntegral u ^ 2 * (1 - u) =
      realStandardGaussianNormalizer ^ 2
    rw [hJ, hZ]
    field_simp [ne_of_gt hGap]
  have hSquare : (J * (1 - u)) ^ 2 <= Z ^ 2 := by
    calc
      _ = (J ^ 2 * (1 - u)) * (1 - u) := by ring
      _ = Z ^ 2 * (1 - u) := by rw [hIdentity]
      _ <= Z ^ 2 * 1 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg Z)
      _ = Z ^ 2 := mul_one _
  have hScaled : J * (1 - u) <= Z := by
    nlinarith only [hSquare, mul_nonneg hJ0 hGap.le, hZ0.le]
  have hFirst : J <= Z / (1 - u) := by
    calc
      J = (J * (1 - u)) * (1 / (1 - u)) := by
        field_simp [ne_of_gt hGap]
      _ <= Z * (1 / (1 - u)) :=
        mul_le_mul_of_nonneg_right hScaled (one_div_pos.mpr hGap).le
      _ = Z / (1 - u) := by ring
  have hFraction : 1 / (1 - u) = u / (1 - u) + 1 := by
    field_simp [ne_of_gt hGap] <;> ring
  have hRatio : 1 / (1 - u) <= Real.exp (u / g) := by
    calc
      _ = u / (1 - u) + 1 := hFraction
      _ <= Real.exp (u / (1 - u)) := Real.add_one_le_exp _
      _ <= Real.exp (u / g) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hu hg hgLe)
  calc
    J <= Z / (1 - u) := hFirst
    _ = Z * (1 / (1 - u)) := by ring
    _ <= Z * Real.exp (u / g) := mul_le_mul_of_nonneg_left hRatio hZ0.le

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def realGaussianQuadraticKernel (r : Iota -> Real) (tau : Real) (x : Iota -> Real) : Real :=
  Real.exp (tau / 2 * Finset.sum Finset.univ (fun i => r i * x i ^ 2)) *
    Finset.prod Finset.univ (fun i => Real.exp (-(1 / 2 : Real) * x i ^ 2))

def realGaussianQuadraticMGF (r : Iota -> Real) (tau : Real) : Real :=
  MeasureTheory.integral gaussianTensorMeasure (realGaussianQuadraticKernel r tau) /
    realStandardGaussianNormalizer ^ Fintype.card Iota

theorem realGaussianQuadraticKernel_factor (r : Iota -> Real) (tau : Real) :
    realGaussianQuadraticKernel r tau = fun x : Iota -> Real =>
      Finset.prod Finset.univ (fun i => Real.exp (-((1 - tau * r i) / 2) * x i ^ 2)) := by
  funext x
  unfold realGaussianQuadraticKernel
  have hSum : tau / 2 * Finset.sum Finset.univ (fun i => r i * x i ^ 2) =
      Finset.sum Finset.univ (fun i => tau * r i * x i ^ 2 / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hSum, Real.exp_sum, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [<- Real.exp_add]
  congr 1
  ring

theorem realGaussianQuadraticKernel_integrable (r : Iota -> Real) (tau : Real)
    (hGap : forall i, 0 < 1 - tau * r i) :
    MeasureTheory.Integrable (realGaussianQuadraticKernel r tau) gaussianTensorMeasure := by
  rw [realGaussianQuadraticKernel_factor]
  unfold gaussianTensorMeasure
  apply MeasureTheory.Integrable.fintype_prod
    (f := fun i (x : Real) => Real.exp (-((1 - tau * r i) / 2) * x ^ 2))
  intro i
  exact integrable_exp_neg_mul_sq (div_pos (hGap i) (by norm_num))

theorem realGaussianQuadraticKernel_integral (r : Iota -> Real) (tau : Real) :
    MeasureTheory.integral gaussianTensorMeasure (realGaussianQuadraticKernel r tau) =
      Finset.prod Finset.univ (fun i => realQuadraticGaussianIntegral (tau * r i)) := by
  rw [realGaussianQuadraticKernel_factor]
  unfold gaussianTensorMeasure
  exact MeasureTheory.integral_fintype_prod_eq_prod
    (fun i (x : Real) => Real.exp (-((1 - tau * r i) / 2) * x ^ 2))

theorem realGaussianQuadraticMGF_zero (r : Iota -> Real) :
    realGaussianQuadraticMGF r 0 = 1 := by
  rw [realGaussianQuadraticMGF, realGaussianQuadraticKernel_integral]
  simp only [zero_mul, realQuadraticGaussianIntegral_zero, Finset.prod_const, Finset.card_univ]
  exact div_self (pow_ne_zero _ (ne_of_gt realStandardGaussianNormalizer_positive))

theorem realGaussianQuadraticMGF_bound (r : Iota -> Real) (tau rho : Real)
    (hTau : 0 <= tau) (hr0 : forall i, 0 <= r i) (hr : forall i, r i <= rho)
    (hGap : 0 < 1 - tau * rho) :
    realGaussianQuadraticMGF r tau <=
      Real.exp (tau / (1 - tau * rho) * Finset.sum Finset.univ r) := by
  let g := 1 - tau * rho
  have hScalar : forall i, realQuadraticGaussianIntegral (tau * r i) <=
      realStandardGaussianNormalizer * Real.exp (tau * r i / g) := by
    intro i
    have hLe : g <= 1 - tau * r i :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left (hr i) hTau) 1
    exact realQuadraticGaussianIntegral_bound _ g (mul_nonneg hTau (hr0 i))
      (lt_of_lt_of_le hGap hLe) hGap hLe
  have hProd : Finset.prod Finset.univ
      (fun i => realQuadraticGaussianIntegral (tau * r i)) <=
      Finset.prod Finset.univ
        (fun i => realStandardGaussianNormalizer * Real.exp (tau * r i / g)) := by
    have hFinite : forall S : Finset Iota,
        Finset.prod S (fun i => realQuadraticGaussianIntegral (tau * r i)) <=
          Finset.prod S
            (fun i => realStandardGaussianNormalizer * Real.exp (tau * r i / g)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi]
        exact mul_le_mul (hScalar i) ih
          (Finset.prod_nonneg (fun j _ => realQuadraticGaussianIntegral_nonnegative _))
          (mul_nonneg realStandardGaussianNormalizer_positive.le (Real.exp_pos _).le)
    exact hFinite Finset.univ
  have hSum : Finset.sum Finset.univ (fun i => tau * r i / g) =
      tau / g * Finset.sum Finset.univ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    <- Real.exp_sum, hSum] at hProd
  unfold realGaussianQuadraticMGF
  rw [realGaussianQuadraticKernel_integral]
  have hDen : 0 < realStandardGaussianNormalizer ^ Fintype.card Iota :=
    pow_pos realStandardGaussianNormalizer_positive _
  calc
    _ = Finset.prod Finset.univ (fun i => realQuadraticGaussianIntegral (tau * r i)) *
        (1 / realStandardGaussianNormalizer ^ Fintype.card Iota) := by ring
    _ <= (realStandardGaussianNormalizer ^ Fintype.card Iota *
        Real.exp (tau / g * Finset.sum Finset.univ r)) *
          (1 / realStandardGaussianNormalizer ^ Fintype.card Iota) :=
      mul_le_mul_of_nonneg_right hProd (one_div_pos.mpr hDen).le
    _ = _ := by
      dsimp only [g]
      field_simp [ne_of_gt hDen]

end PrimeFactorOscillations
