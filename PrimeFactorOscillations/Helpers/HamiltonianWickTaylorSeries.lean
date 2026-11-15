/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import PrimeFactorOscillations.Helpers.HamiltonianWickCoefficientIntegral

/-! # Actual analytic Taylor coefficients of the signed Wick product

The scalar power series used in the finite diagram calculation is the
actual Taylor series, not a separately postulated coefficient model.
Multiplication retains the full Leibniz convolution. The complete even
Taylor coefficient has the exact normalized Gaussian Wick readout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def wickTaylorSeries (f : Complex -> Complex) : PowerSeries Complex :=
  PowerSeries.mk (fun n => Inv.inv (n.factorial : Complex) * iteratedDeriv n f 0)

theorem wickTaylorSeries_coeff (f : Complex -> Complex) (n : Nat) :
    PowerSeries.coeff n (wickTaylorSeries f) =
      Inv.inv (n.factorial : Complex) * iteratedDeriv n f 0 := by
  simp only [wickTaylorSeries, PowerSeries.coeff_mk]

theorem wickTaylorSeries_mul (f g : Complex -> Complex)
    (hf : AnalyticAt Complex f 0) (hg : AnalyticAt Complex g 0) :
    wickTaylorSeries (f * g) = wickTaylorSeries f * wickTaylorSeries g := by
  ext n
  simp only [wickTaylorSeries_coeff,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro i hi
  have hiLe : i <= n := by
    have hLt := Finset.mem_range.mp hi
    omega
  rw [Nat.cast_choose _ hiLe]
  field_simp [Nat.factorial_ne_zero]

theorem wickTaylorSeries_const (c : Complex) :
    wickTaylorSeries (fun _ => c) = PowerSeries.C c := by
  ext n
  by_cases h : n = 0
  case pos => simp [h, wickTaylorSeries_coeff, PowerSeries.coeff_C]
  case neg => simp [h, wickTaylorSeries_coeff, iteratedDeriv_const, PowerSeries.coeff_C]

variable {J : Type*} [DecidableEq J]

theorem wickTaylorSeries_finset_prod (S : Finset J) (f : J -> Complex -> Complex)
    (hf : forall j, Membership.mem S j -> AnalyticAt Complex (f j) 0) :
    wickTaylorSeries (fun x => Finset.prod S (fun j => f j x)) =
      Finset.prod S (fun j => wickTaylorSeries (f j)) := by
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simpa only [Finset.prod_empty, map_one] using wickTaylorSeries_const 1
  | @insert j S hj ih =>
    intro hf
    have hJ := hf j (Finset.mem_insert_self j S)
    have hS : forall k, Membership.mem S k -> AnalyticAt Complex (f k) 0 := by
      intro k hk
      exact hf k (Finset.mem_insert_of_mem hk)
    have hProduct := S.analyticAt_fun_prod hS
    simp_rw [Finset.prod_insert hj]
    change wickTaylorSeries (f j * (fun x => Finset.prod S (fun k => f k x))) = _
    rw [wickTaylorSeries_mul (f j) _ hJ hProduct, ih hS]

theorem wickVertexFunction_differentiable : Differentiable Complex wickVertexFunction := by
  unfold wickVertexFunction
  exact ((differentiable_const (1 : Complex)).add differentiable_id).mul
    (Complex.differentiable_exp.comp
      (differentiable_id.neg.add ((differentiable_id.pow 2).div_const 2)))

theorem wickVertexFunction_analyticAt (x : Complex) :
    AnalyticAt Complex wickVertexFunction x :=
  (wickVertexFunction_differentiable.differentiableOn.analyticOnNhd isOpen_univ)
    x (Set.mem_univ x)

theorem wickTaylorSeries_vertex_scale (Y : Complex) :
    wickTaylorSeries (fun u => wickVertexFunction (Y * u)) =
      wickVertexScalarSeries Y := by
  ext n
  have hSmooth : ContDiff Complex n wickVertexFunction :=
    contDiff_iff_contDiffAt.mpr (fun x => (wickVertexFunction_analyticAt x).contDiffAt)
  rw [wickTaylorSeries_coeff, wickVertexScalarSeries_coeff,
    iteratedDeriv_comp_const_mul hSmooth Y]
  dsimp only
  rw [mul_zero, wickVertexCoefficient_actual]
  ring

variable [Fintype J]

theorem wickVertexProduct_analyticAt (Y : J -> Complex) (u : Complex) :
    AnalyticAt Complex
      (fun w => Finset.prod Finset.univ (fun j => wickVertexFunction (Y j * w))) u := by
  apply Finset.analyticAt_fun_prod
  intro j hj
  exact (wickVertexFunction_analyticAt (Y j * u)).comp
    ((analyticAt_const.mul analyticAt_id) : AnalyticAt Complex (fun w => Y j * w) u)

theorem wickTaylorSeries_vertex_product (Y : J -> Complex) :
    wickTaylorSeries
        (fun u => Finset.prod Finset.univ (fun j => wickVertexFunction (Y j * u))) =
      Finset.prod Finset.univ (fun j => wickVertexScalarSeries (Y j)) := by
  rw [wickTaylorSeries_finset_prod]
  case hf =>
    intro j hj
    exact (wickVertexFunction_analyticAt (Y j * 0)).comp
      ((analyticAt_const.mul analyticAt_id) :
        AnalyticAt Complex (fun u => Y j * u) 0)
  simp_rw [wickTaylorSeries_vertex_scale]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem wickVertexProduct_even_gaussian_readout (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    MeasureTheory.integral gaussianTensorMeasure
        (fun x : Iota -> Real =>
          (Inv.inv ((2 * e).factorial : Complex) *
            iteratedDeriv (2 * e)
              (fun u => Finset.prod Finset.univ
                (fun j => wickVertexFunction (wickGaussianEvaluation z row x j * u))) 0) *
            standardGaussianPolynomialKernel z 1 x) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      Finset.sum (Finset.range (e + 1))
        (fun v => gaussianWickDiagramCoefficient z row e v) := by
  have hKernel : (fun x : Iota -> Real =>
        (Inv.inv ((2 * e).factorial : Complex) *
          iteratedDeriv (2 * e)
            (fun u => Finset.prod Finset.univ
              (fun j => wickVertexFunction (wickGaussianEvaluation z row x j * u))) 0) *
          standardGaussianPolynomialKernel z 1 x) =
      wickGaussianEvenCoefficientKernel z row e := by
    funext x
    rw [<- wickTaylorSeries_coeff, wickTaylorSeries_vertex_product]
    rfl
  rw [hKernel]
  exact wickGaussianEvenCoefficientKernel_full_readout z row e

end PrimeFactorOscillations
