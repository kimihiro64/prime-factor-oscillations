/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianHomogeneousState
import PrimeFactorOscillations.Helpers.HamiltonianWickJetCoefficientMatching

/-! # Gaussian readout of every homogeneous polynomial amplitude coefficient

Only finite signed monomial sums are integrated. The exact amplitude Taylor
coefficient kernel is integrable and reads out the matching homogeneous
Gaussian state. This is the bridge from the finite jet's pointwise amplitude
coefficients to its covariance-degree decomposition.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem wickTaylorSeries_add (f g : Complex -> Complex)
    (hf : AnalyticAt Complex f 0) (hg : AnalyticAt Complex g 0) :
    wickTaylorSeries (f + g) = wickTaylorSeries f + wickTaylorSeries g := by
  ext n
  simp only [wickTaylorSeries_coeff, map_add,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

theorem wickTaylorSeries_power_mul (m : Nat) (a : Complex) :
    wickTaylorSeries (fun u => u ^ m * a) = PowerSeries.monomial m a := by
  ext k
  rw [wickTaylorSeries_coeff, iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
  by_cases h : k = m
  case pos => simp [h, PowerSeries.coeff_monomial, Nat.factorial_ne_zero]
  case neg => simp [h, Ne.symm h, PowerSeries.coeff_monomial]

variable {J : Type*} [DecidableEq J]

theorem wickTaylorSeries_finset_sum (S : Finset J) (f : J -> Complex -> Complex)
    (hf : forall j, Membership.mem S j -> AnalyticAt Complex (f j) 0) :
    wickTaylorSeries (fun u => Finset.sum S (fun j => f j u)) =
      Finset.sum S (fun j => wickTaylorSeries (f j)) := by
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simpa only [Finset.sum_empty, map_zero] using wickTaylorSeries_const 0
  | @insert j S hj ih =>
    intro hf
    have hJ := hf j (Finset.mem_insert_self j S)
    have hS : forall k, Membership.mem S k -> AnalyticAt Complex (f k) 0 := by
      intro k hk
      exact hf k (Finset.mem_insert_of_mem hk)
    have hSum := S.analyticAt_fun_sum hS
    simp_rw [Finset.sum_insert hj]
    change wickTaylorSeries (f j + (fun u => Finset.sum S (fun k => f k u))) = _
    rw [wickTaylorSeries_add (f j) _ hJ hSum, ih hS]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianPolynomial_eval_amplitude (p : MvPolynomial Iota Complex)
    (v : Iota -> Complex) (u : Complex) :
    MvPolynomial.eval (fun j => u * v j) p =
      Finset.sum p.support (fun d =>
        u ^ gaussianStateDegree d *
          (p.coeff d * Finset.prod Finset.univ (fun j => v j ^ d j))) := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold gaussianStateDegree
  ring

theorem gaussianPolynomial_amplitude_coefficient
    (p : MvPolynomial Iota Complex) (v : Iota -> Complex) (k : Nat) :
    PowerSeries.coeff k
        (wickTaylorSeries (fun u => MvPolynomial.eval (fun j => u * v j) p)) =
      Finset.sum (p.support.filter (fun d => gaussianStateDegree d = k))
        (fun d => p.coeff d * Finset.prod Finset.univ (fun j => v j ^ d j)) := by
  have hExpand : (fun u : Complex => MvPolynomial.eval (fun j => u * v j) p) =
      (fun u => Finset.sum p.support (fun d =>
        u ^ gaussianStateDegree d *
          (p.coeff d * Finset.prod Finset.univ (fun j => v j ^ d j)))) := by
    funext u
    exact gaussianPolynomial_eval_amplitude p v u
  rw [hExpand, wickTaylorSeries_finset_sum]
  case hf =>
    intro d hd
    fun_prop
  simp_rw [wickTaylorSeries_power_mul]
  simp only [map_sum, PowerSeries.coeff_monomial, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : gaussianStateDegree d = k
  case pos => simp [h]
  case neg => simp [h, Ne.symm h]

def gaussianPolynomialAmplitudeCoefficientKernel (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (k : Nat) (x : Iota -> Real) : Complex :=
  PowerSeries.coeff k (wickTaylorSeries (fun u =>
      MvPolynomial.eval
        (fun j => u * (complexGaussianSquareRoot (z j) * (x j : Complex))) p)) *
    standardGaussianPolynomialKernel z 1 x

theorem gaussianPolynomialAmplitudeCoefficientKernel_expansion
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (k : Nat) :
    gaussianPolynomialAmplitudeCoefficientKernel z p k =
      (fun x => Finset.sum (p.support.filter (fun d => gaussianStateDegree d = k))
        (fun d => p.coeff d *
          gaussianTensorTiltKernel (fun _ => 0)
            (fun j => complexGaussianSquareRoot (z j)) (fun j => d j) x)) := by
  funext x
  unfold gaussianPolynomialAmplitudeCoefficientKernel
  rw [gaussianPolynomial_amplitude_coefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [standardGaussianPolynomialKernel, gaussianMvTiltKernel, map_one, one_mul,
    gaussianTensorTiltKernel, Finset.prod_mul_distrib]
  ring

theorem gaussianPolynomialAmplitudeCoefficientKernel_integrable
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (k : Nat) :
    MeasureTheory.Integrable (gaussianPolynomialAmplitudeCoefficientKernel z p k)
      gaussianTensorMeasure := by
  rw [gaussianPolynomialAmplitudeCoefficientKernel_expansion]
  apply MeasureTheory.integrable_finsetSum
  intro d hd
  exact (gaussianTensorTiltKernel_integrable (fun _ => 0)
    (fun j => complexGaussianSquareRoot (z j)) (fun _ => by norm_num)
    (fun j => d j)).const_mul (p.coeff d)

theorem gaussianPolynomialAmplitudeCoefficientKernel_normalized
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (k : Nat) :
    MeasureTheory.integral gaussianTensorMeasure
        (gaussianPolynomialAmplitudeCoefficientKernel z p k) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      gaussianPolynomialDegreeState z p k := by
  rw [gaussianPolynomialAmplitudeCoefficientKernel_expansion,
    MeasureTheory.integral_finsetSum
      (p.support.filter (fun d => gaussianStateDegree d = k))
      (fun d _ => (gaussianTensorTiltKernel_integrable (fun _ => 0)
        (fun j => complexGaussianSquareRoot (z j)) (fun _ => by norm_num)
        (fun j => d j)).const_mul (p.coeff d)), Finset.sum_div]
  unfold gaussianPolynomialDegreeState
  apply Finset.sum_congr rfl
  intro d hd
  rw [MeasureTheory.integral_const_mul, mul_div_assoc,
    standardGaussianTensor_normalized]

theorem wickGaussianEvaluation_eigenRows (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (z : Iota -> Complex) (x : Iota -> Real) :
    wickGaussianEvaluation z (realGaussianEigenRows M hM) x =
      realGaussianWeightedVector M hM (fun j => complexGaussianSquareRoot (z j)) x := by
  funext i
  simp only [wickGaussianEvaluation, realGaussianWeightedVector, gaussianLinearForm,
    realGaussianEigenRows, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem wickFiniteGaussianJetPolynomial_amplitude_eval (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (z : Iota -> Complex) (H : Nat)
    (u : Complex) (x : Iota -> Real) :
    MvPolynomial.eval
        (fun j => u * (complexGaussianSquareRoot (z j) * (x j : Complex)))
        (wickFiniteGaussianJetPolynomial M hM H) =
      wickFiniteGaussianJet
        (fun i => wickGaussianEvaluation z (realGaussianEigenRows M hM) x i * u) H := by
  have hCoordinates :
      (fun j => u * (complexGaussianSquareRoot (z j) * (x j : Complex))) =
      (fun j => (u * complexGaussianSquareRoot (z j)) * (x j : Complex)) := by
    funext j
    ring
  have hVector :
      realGaussianWeightedVector M hM (fun j => u * complexGaussianSquareRoot (z j)) x =
      (fun i => wickGaussianEvaluation z (realGaussianEigenRows M hM) x i * u) := by
    rw [wickGaussianEvaluation_eigenRows]
    funext i
    unfold realGaussianWeightedVector
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hCoordinates, wickFiniteGaussianJetPolynomial_eval, hVector]

theorem gaussianPolynomialAmplitudeCoefficientKernel_finiteJet
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (z : Iota -> Complex) (H k : Nat) :
    gaussianPolynomialAmplitudeCoefficientKernel z (wickFiniteGaussianJetPolynomial M hM H) k =
      (fun x : Iota -> Real =>
        (Inv.inv (k.factorial : Complex) *
          iteratedDeriv k
            (fun u => wickFiniteGaussianJet
              (fun i => wickGaussianEvaluation z (realGaussianEigenRows M hM) x i * u) H) 0) *
          standardGaussianPolynomialKernel z 1 x) := by
  funext x
  unfold gaussianPolynomialAmplitudeCoefficientKernel
  have hFunction :
      (fun u : Complex => MvPolynomial.eval
        (fun j => u * (complexGaussianSquareRoot (z j) * (x j : Complex)))
        (wickFiniteGaussianJetPolynomial M hM H)) =
      (fun u => wickFiniteGaussianJet
        (fun i => wickGaussianEvaluation z (realGaussianEigenRows M hM) x i * u) H) := by
    funext u
    exact wickFiniteGaussianJetPolynomial_amplitude_eval M hM z H u x
  rw [hFunction, wickTaylorSeries_coeff]

variable [Nonempty Iota]

theorem wickFiniteGaussianJet_degree_readout
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (z : Iota -> Complex)
    (H e : Nat)
    (hZero : forall x : Iota -> Real,
      Finset.sum Finset.univ (wickGaussianEvaluation z (realGaussianEigenRows M hM) x) = 0)
    (he : e < H) :
    gaussianPolynomialDegreeState z (wickFiniteGaussianJetPolynomial M hM H) (2 * e) =
      Finset.sum (Finset.range (e + 1))
        (fun v => gaussianWickDiagramCoefficient z (realGaussianEigenRows M hM) e v) := by
  rw [<- gaussianPolynomialAmplitudeCoefficientKernel_normalized,
    gaussianPolynomialAmplitudeCoefficientKernel_finiteJet]
  exact wickFiniteGaussianJet_even_gaussian_readout z (realGaussianEigenRows M hM)
    H e hZero he

theorem realGaussianQuotient_finiteJet_degree_readout
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (H e : Nat) (he : e < H) :
    gaussianPolynomialDegreeState
        (fun j => s * realGaussianEigenVariances M hM j /
          (1 + s * realGaussianEigenVariances M hM j))
        (wickFiniteGaussianJetPolynomial M hM H) (2 * e) =
      Finset.sum (Finset.range (e + 1)) (fun v =>
        gaussianWickDiagramCoefficient
          (fun j => s * realGaussianEigenVariances M hM j /
            (1 + s * realGaussianEigenVariances M hM j))
          (realGaussianEigenRows M hM) e v) := by
  apply wickFiniteGaussianJet_degree_readout M hM _ H e _ he
  intro x
  rw [wickGaussianEvaluation_eigenRows]
  exact realGaussianQuotientVector_zero_sum M hM s hCol x

end PrimeFactorOscillations
