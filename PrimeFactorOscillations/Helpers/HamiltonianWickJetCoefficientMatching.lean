/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAnalyticRayOrder
import PrimeFactorOscillations.Helpers.HamiltonianGaussianFiniteJetIntegral
import PrimeFactorOscillations.Helpers.HamiltonianWickTaylorSeries

/-! # Homogeneous finite-jet coefficients retain the full Wick profiles

The finite jet agrees with the actual signed product in every amplitude
degree below twice the exponential truncation order. The proof uses the
full compensated error, then the positive-real analytic order theorem.
Every low even coefficient has the complete actual Gaussian readout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem wickFiniteGaussianJet_analyticAt (Y : J -> Complex) (H : Nat) (u : Complex) :
    AnalyticAt Complex (fun w => wickFiniteGaussianJet (fun j => Y j * w) H) u := by
  unfold wickFiniteGaussianJet
  fun_prop

theorem wickSquareMass_scale_right (Y : J -> Complex) (t : Real) :
    collectiveSquareMass (fun j => Y j * (t : Complex)) =
      collectiveSquareMass Y * t ^ 2 := by
  unfold collectiveSquareMass
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_mul]

variable [Nonempty J]

theorem wickFiniteGaussianJet_taylor_coefficient (Y : J -> Complex)
    (H k : Nat) (hZero : Finset.sum Finset.univ Y = 0) (hk : k < 2 * H) :
    PowerSeries.coeff k
        (Finset.prod Finset.univ (fun j => wickVertexScalarSeries (Y j))) =
      PowerSeries.coeff k
        (wickTaylorSeries (fun u => wickFiniteGaussianJet (fun j => Y j * u) H)) := by
  let f := fun u : Complex =>
    Finset.prod Finset.univ (fun j => wickVertexFunction (Y j * u))
  let g := fun u : Complex => wickFiniteGaussianJet (fun j => Y j * u) H
  let W := collectiveSquareMass Y
  let C := (W / 2) ^ H * Real.exp W
  have hW : 0 <= W := collectiveSquareMass_nonnegative Y
  have hC : 0 <= C := mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hf : AnalyticAt Complex f 0 := wickVertexProduct_analyticAt Y 0
  have hg : AnalyticAt Complex g 0 := wickFiniteGaussianJet_analyticAt Y H 0
  have hBound : forall t : Real, 0 < t -> t < 1 ->
      norm ((f - g) (t : Complex)) <= C * t ^ (2 * H) := by
    intro t ht htOne
    have hZeroScaled : Finset.sum Finset.univ (fun j => Y j * (t : Complex)) = 0 := by
      rw [<- Finset.sum_mul, hZero, zero_mul]
    have hScaled := wickFiniteGaussianJet_remainder_bound
      (fun j => Y j * (t : Complex)) H hZeroScaled
    rw [wickSquareMass_scale_right] at hScaled
    have hSquare : t ^ 2 <= 1 := by nlinarith
    have hExp : Real.exp (W * t ^ 2) <= Real.exp W :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hPower : (W * t ^ 2 / 2) ^ H = (W / 2) ^ H * t ^ (2 * H) := by
      have hBase : W * t ^ 2 / 2 = (W / 2) * t ^ 2 := by ring
      rw [hBase, mul_pow, <- pow_mul]
    change norm (f (t : Complex) - g (t : Complex)) <= C * t ^ (2 * H)
    calc
      _ <= (W * t ^ 2 / 2) ^ H * Real.exp (W * t ^ 2) := hScaled
      _ <= (W * t ^ 2 / 2) ^ H * Real.exp W :=
        mul_le_mul_of_nonneg_left hExp (pow_nonneg (by positivity) _)
      _ = _ := by rw [hPower]; dsimp only [C]; ring
  have hDerivative := hamiltonian_derivatives_zero_of_positive_ray (f - g)
    (hf.sub hg) (2 * H) C 1 hC (by norm_num) hBound k hk
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt] at hDerivative
  have hEqual : iteratedDeriv k f 0 = iteratedDeriv k g 0 := sub_eq_zero.mp hDerivative
  rw [<- wickTaylorSeries_vertex_product Y]
  change PowerSeries.coeff k (wickTaylorSeries f) = PowerSeries.coeff k (wickTaylorSeries g)
  rw [wickTaylorSeries_coeff, wickTaylorSeries_coeff, hEqual]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem wickFiniteGaussianJet_even_gaussian_readout
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (H e : Nat)
    (hZero : forall x : Iota -> Real,
      Finset.sum Finset.univ (wickGaussianEvaluation z row x) = 0)
    (he : e < H) :
    MeasureTheory.integral gaussianTensorMeasure
        (fun x : Iota -> Real =>
          (Inv.inv ((2 * e).factorial : Complex) *
            iteratedDeriv (2 * e)
              (fun u => wickFiniteGaussianJet
                (fun j => wickGaussianEvaluation z row x j * u) H) 0) *
            standardGaussianPolynomialKernel z 1 x) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      Finset.sum (Finset.range (e + 1))
        (fun v => gaussianWickDiagramCoefficient z row e v) := by
  have hKernel : (fun x : Iota -> Real =>
        (Inv.inv ((2 * e).factorial : Complex) *
          iteratedDeriv (2 * e)
            (fun u => wickFiniteGaussianJet
              (fun j => wickGaussianEvaluation z row x j * u) H) 0) *
          standardGaussianPolynomialKernel z 1 x) =
      (fun x : Iota -> Real =>
        (Inv.inv ((2 * e).factorial : Complex) *
          iteratedDeriv (2 * e)
            (fun u => Finset.prod Finset.univ
              (fun j => wickVertexFunction (wickGaussianEvaluation z row x j * u))) 0) *
          standardGaussianPolynomialKernel z 1 x) := by
    funext x
    have hc := wickFiniteGaussianJet_taylor_coefficient (wickGaussianEvaluation z row x)
      H (2 * e) (hZero x) (by omega)
    rw [<- wickTaylorSeries_vertex_product] at hc
    simp only [wickTaylorSeries_coeff] at hc
    exact congrArg (fun a : Complex => a * standardGaussianPolynomialKernel z 1 x) hc.symm
  rw [hKernel]
  exact wickVertexProduct_even_gaussian_readout z row e

end PrimeFactorOscillations
