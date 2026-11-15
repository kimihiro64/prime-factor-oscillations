/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import PrimeFactorOscillations.Helpers.HamiltonianGammaShiftedTails
import PrimeFactorOscillations.Helpers.HamiltonianGaussianRookBounds

/-! # The actual joint Gaussian and shifted-Gamma tail

Small and large quadratic energies are coupled in one pointwise
inequality, then integrated against the actual Gaussian density. The
two Gaussian exponential moments remain explicit for the stochastic
constant consumer. This controls only the retained analytic remainder.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

instance gammaHalfLine_sigmaFinite : SigmaFinite gammaHalfLine := by
  unfold gammaHalfLine
  infer_instance

theorem gammaShiftOutsideAverage_nonnegative (n : Nat) (w ell r : Real)
    (hw : 0 <= w) : 0 <= gammaShiftOutsideAverage n w ell r := by
  unfold gammaShiftOutsideAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply integral_nonneg_of_ae
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have h0 : 0 <= Real.exp (-t) * (t + w) ^ n :=
    mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (add_nonneg (show 0 <= t from le_of_lt ht) hw) _)
  by_cases hE : Membership.mem (Set.compl (Set.Icc ell r)) t
  case pos => simpa [Set.indicator, hE] using h0
  case neg => simp [Set.indicator, hE]

theorem gammaShiftOutsideAverage_two_tilts (n : Nat) (w delta tau : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) (hw : 0 <= w) (hTau : 1 <= tau) :
    gammaShiftOutsideAverage n w
        ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)) <=
      2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304) * Real.exp w +
        Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) * Real.exp (tau * w) := by
  by_cases hSmall : w <= delta * (n : Real) / 16
  case pos =>
    have h := gammaShiftOutsideAverage_delta n w delta hDelta0 hDelta1 hN hw hSmall
    calc
      _ <= 2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304) * Real.exp w := by
        convert! h using 1 <;> ring
      _ <= _ := le_add_of_nonneg_right
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  case neg =>
    have hExp : Real.exp w <=
        Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) * Real.exp (tau * w) := by
      rw [<- Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg (sub_nonneg.mpr hTau)
        (sub_nonneg.mpr (le_of_not_ge hSmall))
      nlinarith
    calc
      _ <= Real.exp w := gammaShiftOutsideAverage_le_full n w _ _ hw
      _ <= _ := le_trans hExp (le_add_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (Real.exp_pos _).le))

theorem gammaShiftOutsideAverage_measurable (n : Nat) (ell r : Real) :
    Measurable (fun w : Real => gammaShiftOutsideAverage n w ell r) := by
  let E := Set.compl (Set.Icc ell r)
  have hE : MeasurableSet E := measurableSet_Icc.compl
  let F := fun p : Prod Real Real =>
    Real.exp (-p.2) * (p.2 + p.1) ^ n *
      Set.indicator E (fun _ => (1 : Real)) p.2
  have hBase : Continuous (fun p : Prod Real Real =>
      Real.exp (-p.2) * (p.2 + p.1) ^ n) := by fun_prop
  have hInd : Measurable (fun p : Prod Real Real =>
      Set.indicator E (fun _ => (1 : Real)) p.2) :=
    (measurable_const.indicator hE).comp measurable_snd
  have hF : StronglyMeasurable F := (hBase.measurable.mul hInd).stronglyMeasurable
  have hIntegral : StronglyMeasurable
      (fun w : Real => MeasureTheory.integral gammaHalfLine (fun t => F (w, t))) :=
    hF.integral_prod_right'
  have hActual : (fun w : Real => gammaShiftOutsideAverage n w ell r) =
      fun w => Inv.inv (n.factorial : Real) *
        MeasureTheory.integral gammaHalfLine (fun t => F (w, t)) := by
    funext w
    unfold gammaShiftOutsideAverage
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only [F, E]
      by_cases h : Membership.mem (Set.compl (Set.Icc ell r)) t <;>
        simp [Set.indicator, h])
  rw [hActual]
  exact measurable_const.mul hIntegral.measurable

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

instance gaussianTensorMeasure_sigmaFinite :
    SigmaFinite (gaussianTensorMeasure (Iota := Iota)) := by
  unfold gaussianTensorMeasure
  infer_instance

def realGaussianSquareHalfMass (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (x : Iota -> Real) : Real :=
  Finset.sum Finset.univ (fun i => norm (realGaussianVector M hM x i) ^ 2) / 2

def realStandardGaussianDensity (x : Iota -> Real) : Real :=
  Finset.prod Finset.univ (fun i => Real.exp (-(1 / 2 : Real) * x i ^ 2))

theorem realGaussianSquareHalfMass_nonnegative (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (x : Iota -> Real) :
    0 <= realGaussianSquareHalfMass M hM x :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num)

theorem realGaussianSquareHalfMass_continuous (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) : Continuous (realGaussianSquareHalfMass M hM) := by
  unfold realGaussianSquareHalfMass realGaussianVector
  fun_prop

theorem realStandardGaussianDensity_nonnegative (x : Iota -> Real) :
    0 <= realStandardGaussianDensity x :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

theorem realStandardGaussianDensity_continuous :
    Continuous (realStandardGaussianDensity (Iota := Iota)) := by
  unfold realStandardGaussianDensity
  fun_prop

theorem realSpectralGaussianQuadraticKernel_half_mass (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau : Real) (x : Iota -> Real) :
    realSpectralGaussianQuadraticKernel M hM tau x =
      Real.exp (tau * realGaussianSquareHalfMass M hM x) *
        realStandardGaussianDensity x := by
  unfold realSpectralGaussianQuadraticKernel realGaussianSquareHalfMass
    realStandardGaussianDensity
  congr 2
  ring

def realGaussianGammaOutsideKernel (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real) (x : Iota -> Real) : Real :=
  gammaShiftOutsideAverage n (realGaussianSquareHalfMass M hM x)
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)) *
    realStandardGaussianDensity x

def realGaussianGammaOutsideAverage (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real) : Real :=
  MeasureTheory.integral gaussianTensorMeasure
      (realGaussianGammaOutsideKernel M hM n delta) /
    realStandardGaussianNormalizer ^ Fintype.card Iota

theorem realGaussianGammaOutsideKernel_nonnegative (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real) (x : Iota -> Real) :
    0 <= realGaussianGammaOutsideKernel M hM n delta x :=
  mul_nonneg (gammaShiftOutsideAverage_nonnegative n _ _ _
    (realGaussianSquareHalfMass_nonnegative M hM x))
    (realStandardGaussianDensity_nonnegative x)

theorem realGaussianGammaOutsideKernel_measurable (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real) :
    Measurable (realGaussianGammaOutsideKernel M hM n delta) := by
  apply Measurable.mul
    ((gammaShiftOutsideAverage_measurable n _ _).comp
      (realGaussianSquareHalfMass_continuous M hM).measurable)
    realStandardGaussianDensity_continuous.measurable

theorem realGaussianGammaOutsideKernel_le_envelope (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real) (x : Iota -> Real) :
    realGaussianGammaOutsideKernel M hM n delta x <=
      realSpectralGaussianQuadraticKernel M hM 1 x := by
  rw [realSpectralGaussianQuadraticKernel_half_mass, one_mul]
  exact mul_le_mul_of_nonneg_right
    (gammaShiftOutsideAverage_le_full n _ _ _
      (realGaussianSquareHalfMass_nonnegative M hM x))
    (realStandardGaussianDensity_nonnegative x)

theorem realGaussianGammaOutsideKernel_integrable (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta rho : Real)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho) :
    Integrable (realGaussianGammaOutsideKernel M hM n delta) gaussianTensorMeasure := by
  have hEnvelope := realSpectralGaussianQuadraticKernel_integrable M hM 1 rho
    zero_le_one hNorm (by simpa only [one_mul] using hGap)
  apply hEnvelope.mono' (realGaussianGammaOutsideKernel_measurable M hM n delta).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (realGaussianGammaOutsideKernel_nonnegative M hM n delta x)]
    exact realGaussianGammaOutsideKernel_le_envelope M hM n delta x)

theorem realGaussianGammaOutsideAverage_two_tilts (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta tau rho : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) (hTau : 1 <= tau)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho)
    (hTauGap : 0 < 1 - tau * rho) :
    realGaussianGammaOutsideAverage M hM n delta <=
      (2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304)) *
          realSpectralGaussianQuadraticMGF M hM 1 +
        Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) *
          realSpectralGaussianQuadraticMGF M hM tau := by
  let c1 := 2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304)
  let c2 := Real.exp (-(tau - 1) * (delta * (n : Real) / 16))
  have hInt := realGaussianGammaOutsideKernel_integrable M hM n delta rho hNorm hGap
  have hInt1 := realSpectralGaussianQuadraticKernel_integrable M hM 1 rho
    zero_le_one hNorm (by simpa only [one_mul] using hGap)
  have hIntTau := realSpectralGaussianQuadraticKernel_integrable M hM tau rho
    (le_trans zero_le_one hTau) hNorm hTauGap
  have hDom : forall x : Iota -> Real,
      realGaussianGammaOutsideKernel M hM n delta x <=
        c1 * realSpectralGaussianQuadraticKernel M hM 1 x +
          c2 * realSpectralGaussianQuadraticKernel M hM tau x := by
    intro x
    have h := mul_le_mul_of_nonneg_right
      (gammaShiftOutsideAverage_two_tilts n (realGaussianSquareHalfMass M hM x)
        delta tau hDelta0 hDelta1 hN
        (realGaussianSquareHalfMass_nonnegative M hM x) hTau)
      (realStandardGaussianDensity_nonnegative x)
    rw [realSpectralGaussianQuadraticKernel_half_mass,
      realSpectralGaussianQuadraticKernel_half_mass, one_mul]
    unfold realGaussianGammaOutsideKernel
    convert! h using 1 <;> dsimp only [c1, c2] <;> ring
  have hIntegral := integral_mono hInt
    ((hInt1.const_mul c1).add (hIntTau.const_mul c2)) hDom
  have hDen : 0 <= realStandardGaussianNormalizer ^ Fintype.card Iota :=
    (pow_pos realStandardGaussianNormalizer_positive _).le
  unfold realGaussianGammaOutsideAverage realSpectralGaussianQuadraticMGF
  change MeasureTheory.integral gaussianTensorMeasure
      (realGaussianGammaOutsideKernel M hM n delta) <=
    MeasureTheory.integral gaussianTensorMeasure (fun x =>
      c1 * realSpectralGaussianQuadraticKernel M hM 1 x +
        c2 * realSpectralGaussianQuadraticKernel M hM tau x) at hIntegral
  rw [integral_add (hInt1.const_mul c1) (hIntTau.const_mul c2),
    integral_const_mul, integral_const_mul] at hIntegral
  calc
    _ <= (c1 * MeasureTheory.integral gaussianTensorMeasure
            (realSpectralGaussianQuadraticKernel M hM 1) +
          c2 * MeasureTheory.integral gaussianTensorMeasure
            (realSpectralGaussianQuadraticKernel M hM tau)) /
        realStandardGaussianNormalizer ^ Fintype.card Iota :=
      div_le_div_of_nonneg_right hIntegral hDen
    _ = _ := by dsimp only [c1, c2]; ring

end PrimeFactorOscillations
