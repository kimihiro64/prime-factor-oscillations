/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStochasticGammaTail

/-! # Full product integrability and Gaussian/Gamma Fubini transfer

The collective quadratic envelope proves actual joint integrability
before the order of integration is changed. Every overlap in the
Gaussian energy and every original outside-window endpoint is retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def realGaussianGammaJointEnvelope (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta : Real)
    (p : Prod (Iota -> Real) Real) : Real :=
  Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
    Set.indicator (Set.compl (Set.Icc
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4))))
      (fun t : Real => Real.exp (-t) *
        (t + realGaussianSquareHalfMass M hM p.1) ^ n) p.2

theorem realGaussianGammaJointEnvelope_stronglyMeasurable
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (n : Nat) (delta : Real) :
    StronglyMeasurable (realGaussianGammaJointEnvelope M hM n delta) := by
  let E := Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))
  have hE : MeasurableSet E := measurableSet_Icc.compl
  have hBase : Continuous (fun p : Prod (Iota -> Real) Real =>
      Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
        (Real.exp (-p.2) * (p.2 + realGaussianSquareHalfMass M hM p.1) ^ n)) := by
    unfold realStandardGaussianDensity realGaussianSquareHalfMass realGaussianVector
    fun_prop
  have hInd : Measurable (fun p : Prod (Iota -> Real) Real =>
      Set.indicator E (fun _ => (1 : Real)) p.2) :=
    (measurable_const.indicator hE).comp measurable_snd
  have hFun : realGaussianGammaJointEnvelope M hM n delta =
      fun p : Prod (Iota -> Real) Real =>
        (Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
          (Real.exp (-p.2) * (p.2 + realGaussianSquareHalfMass M hM p.1) ^ n)) *
            Set.indicator E (fun _ => (1 : Real)) p.2 := by
    funext p
    unfold realGaussianGammaJointEnvelope
    dsimp only [E]
    by_cases h : Membership.mem (Set.compl (Set.Icc
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) p.2 <;>
      simp [Set.indicator, h]
  rw [hFun]
  exact (hBase.measurable.mul hInd).stronglyMeasurable

theorem realGaussianGammaJointEnvelope_inner_integrable
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (n : Nat) (delta : Real)
    (x : Iota -> Real) :
    Integrable (fun t => realGaussianGammaJointEnvelope M hM n delta (x, t))
      gammaHalfLine := by
  have h := (gammaShiftKernel_plain_integrable n (realGaussianSquareHalfMass M hM x)
    (realGaussianSquareHalfMass_nonnegative M hM x)).indicator
      (s := Set.compl (Set.Icc ((n : Real) / (1 + delta / 4))
        ((n : Real) / (1 - delta / 4)))) (measurableSet_Icc.compl)
  exact h.const_mul (Inv.inv (n.factorial : Real) * realStandardGaussianDensity x)

theorem realGaussianGammaJointEnvelope_inner_nonnegative
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (n : Nat) (delta : Real)
    (x : Iota -> Real) :
    Filter.Eventually (fun t =>
      0 <= realGaussianGammaJointEnvelope M hM n delta (x, t)) (ae gammaHalfLine) := by
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  unfold realGaussianGammaJointEnvelope
  apply mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (realStandardGaussianDensity_nonnegative x))
  by_cases h : Membership.mem (Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t
  case pos =>
    simp only [Set.indicator_of_mem h]
    exact mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (add_nonneg (show 0 <= t from le_of_lt ht)
        (realGaussianSquareHalfMass_nonnegative M hM x)) _)
  case neg => simp [Set.indicator, h]

theorem realGaussianGammaJointEnvelope_inner_integral
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (n : Nat) (delta : Real)
    (x : Iota -> Real) :
    MeasureTheory.integral gammaHalfLine
        (fun t => realGaussianGammaJointEnvelope M hM n delta (x, t)) =
      realGaussianGammaOutsideKernel M hM n delta x := by
  unfold realGaussianGammaJointEnvelope realGaussianGammaOutsideKernel
    gammaShiftOutsideAverage
  dsimp only
  rw [integral_const_mul]
  ring

theorem realGaussianGammaJointEnvelope_integrable (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta rho : Real)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho) :
    Integrable (realGaussianGammaJointEnvelope M hM n delta)
      (gaussianTensorMeasure.prod gammaHalfLine) := by
  apply (integrable_prod_iff
    (realGaussianGammaJointEnvelope_stronglyMeasurable M hM n delta).aestronglyMeasurable).mpr
  refine And.intro (Filter.Eventually.of_forall (fun x =>
    realGaussianGammaJointEnvelope_inner_integrable M hM n delta x)) ?_
  have hNormInner :
      (fun x : Iota -> Real => MeasureTheory.integral gammaHalfLine
        (fun t => norm (realGaussianGammaJointEnvelope M hM n delta (x, t)))) =
      realGaussianGammaOutsideKernel M hM n delta := by
    funext x
    rw [<- realGaussianGammaJointEnvelope_inner_integral M hM n delta x]
    apply integral_congr_ae
    exact (realGaussianGammaJointEnvelope_inner_nonnegative M hM n delta x).mono
      (fun t ht => Real.norm_of_nonneg ht)
  rw [hNormInner]
  exact realGaussianGammaOutsideKernel_integrable M hM n delta rho hNorm hGap

theorem realGaussianGammaJointEnvelope_total (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (n : Nat) (delta rho : Real)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho) :
    MeasureTheory.integral gammaHalfLine (fun t =>
        MeasureTheory.integral gaussianTensorMeasure (fun x =>
          realGaussianGammaJointEnvelope M hM n delta (x, t))) =
      MeasureTheory.integral gaussianTensorMeasure
        (realGaussianGammaOutsideKernel M hM n delta) := by
  have hInt := realGaussianGammaJointEnvelope_integrable M hM n delta rho hNorm hGap
  calc
    _ = MeasureTheory.integral gaussianTensorMeasure (fun x =>
        MeasureTheory.integral gammaHalfLine (fun t =>
          realGaussianGammaJointEnvelope M hM n delta (x, t))) :=
      (integral_integral_swap (f := fun x t =>
        realGaussianGammaJointEnvelope M hM n delta (x, t)) hInt).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (realGaussianGammaJointEnvelope_inner_integral M hM n delta)

def realGaussianGammaJointProfile {n : Nat}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (hM : M.IsHermitian) (delta : Real)
    (p : Prod (Sum (Fin n) (Fin n) -> Real) Real) : Real :=
  Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
    Set.indicator (Set.compl (Set.Icc
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4))))
      (fun t : Real => Real.exp (-t) * t ^ n *
        Finset.prod Finset.univ (fun i =>
          norm (1 + (Real.sqrt ((n : Real) / t) : Complex) *
            realGaussianVector M hM p.1 i))) p.2

theorem realGaussianGammaJointProfile_stronglyMeasurable {n : Nat}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (hM : M.IsHermitian) (delta : Real) :
    StronglyMeasurable (realGaussianGammaJointProfile M hM delta) := by
  let E := Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))
  have hE : MeasurableSet E := measurableSet_Icc.compl
  have hBase : Measurable (fun p : Prod (Sum (Fin n) (Fin n) -> Real) Real =>
      Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
        (Real.exp (-p.2) * p.2 ^ n *
          Finset.prod Finset.univ (fun i =>
            norm (1 + (Real.sqrt ((n : Real) / p.2) : Complex) *
              realGaussianVector M hM p.1 i)))) := by
    unfold realStandardGaussianDensity realGaussianVector
    fun_prop
  have hInd : Measurable (fun p : Prod (Sum (Fin n) (Fin n) -> Real) Real =>
      Set.indicator E (fun _ => (1 : Real)) p.2) :=
    (measurable_const.indicator hE).comp measurable_snd
  have hFun : realGaussianGammaJointProfile M hM delta =
      fun p : Prod (Sum (Fin n) (Fin n) -> Real) Real =>
        (Inv.inv (n.factorial : Real) * realStandardGaussianDensity p.1 *
          (Real.exp (-p.2) * p.2 ^ n *
            Finset.prod Finset.univ (fun i =>
              norm (1 + (Real.sqrt ((n : Real) / p.2) : Complex) *
                realGaussianVector M hM p.1 i)))) *
                  Set.indicator E (fun _ => (1 : Real)) p.2 := by
    funext p
    unfold realGaussianGammaJointProfile
    dsimp only [E]
    by_cases h : Membership.mem (Set.compl (Set.Icc
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) p.2 <;>
      simp [Set.indicator, h]
  rw [hFun]
  exact (hBase.mul hInd).stronglyMeasurable

theorem realGaussianGammaJointProfile_norm_le {n : Nat}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (hM : M.IsHermitian) (delta : Real) (hN : 0 < n)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Sum (Fin n) (Fin n) -> Real) (t : Real) (ht : 0 < t) :
    norm (realGaussianGammaJointProfile M hM delta (x, t)) <=
      realGaussianGammaJointEnvelope M hM n delta (x, t) := by
  have hCard : 0 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hN
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp hCard
  have hD := realStandardGaussianDensity_nonnegative x
  have hWeight : 0 <= Inv.inv (n.factorial : Real) * realStandardGaussianDensity x :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hD
  have hProduct0 : 0 <= Finset.prod Finset.univ (fun i =>
      norm (1 + (Real.sqrt ((n : Real) / t) : Complex) *
        realGaussianVector M hM x i)) :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hNonneg : 0 <= realGaussianGammaJointProfile M hM delta (x, t) := by
    unfold realGaussianGammaJointProfile
    apply mul_nonneg hWeight
    by_cases h : Membership.mem (Set.compl (Set.Icc
      ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t
    case pos =>
      simp only [Set.indicator_of_mem h]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _)) hProduct0
    case neg => simp [Set.indicator, h]
  rw [Real.norm_of_nonneg hNonneg]
  unfold realGaussianGammaJointProfile realGaussianGammaJointEnvelope
  by_cases h : Membership.mem (Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t
  case neg => simp [Set.indicator, h]
  case pos =>
    simp only [Set.indicator_of_mem h]
    apply mul_le_mul_of_nonneg_left _ hWeight
    have hProduct := collective_gamma_product_bound
      (realGaussianVector M hM x) (realGaussianVector_zero_sum M hM hCol x) t ht
    have hPolynomial :
        t ^ n * (1 + collectiveSquareMass (realGaussianVector M hM x) / (2 * t)) ^ n =
          (t + realGaussianSquareHalfMass M hM x) ^ n := by
      rw [<- mul_pow]
      congr 1
      unfold collectiveSquareMass realGaussianSquareHalfMass
      field_simp [ne_of_gt ht]
    calc
      _ <= (Real.exp (-t) * t ^ n) *
          (1 + collectiveSquareMass (realGaussianVector M hM x) / (2 * t)) ^ n :=
        mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_fin] using hProduct)
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _))
      _ = _ := by rw [mul_assoc, hPolynomial]

theorem realGaussianGamma_positive_second_ae :
    Filter.Eventually (fun p : Prod (Iota -> Real) Real => 0 < p.2)
      (ae (gaussianTensorMeasure.prod gammaHalfLine)) := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioi.preimage measurable_snd)).mpr
  exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioi)

theorem realGaussianGammaJointProfile_integrable {n : Nat}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (hM : M.IsHermitian) (delta rho : Real) (hN : 0 < n)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho) :
    Integrable (realGaussianGammaJointProfile M hM delta)
      (gaussianTensorMeasure.prod gammaHalfLine) := by
  apply (realGaussianGammaJointEnvelope_integrable M hM n delta rho hNorm hGap).mono'
    (realGaussianGammaJointProfile_stronglyMeasurable M hM delta).aestronglyMeasurable
  exact realGaussianGamma_positive_second_ae.mono (fun p ht =>
    realGaussianGammaJointProfile_norm_le M hM delta hN hCol p.1 p.2 ht)

theorem realGaussianGammaJointProfile_total_le {n : Nat}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (hM : M.IsHermitian) (delta rho : Real) (hN : 0 < n)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - rho) :
    MeasureTheory.integral gammaHalfLine (fun t =>
        MeasureTheory.integral gaussianTensorMeasure (fun x =>
          realGaussianGammaJointProfile M hM delta (x, t))) <=
      MeasureTheory.integral gaussianTensorMeasure
        (realGaussianGammaOutsideKernel M hM n delta) := by
  have hP := realGaussianGammaJointProfile_integrable M hM delta rho hN hCol hNorm hGap
  have hQ := realGaussianGammaJointEnvelope_integrable M hM n delta rho hNorm hGap
  have hDom : Filter.Eventually (fun p =>
      realGaussianGammaJointProfile M hM delta p <=
        realGaussianGammaJointEnvelope M hM n delta p)
      (ae (gaussianTensorMeasure.prod gammaHalfLine)) :=
    realGaussianGamma_positive_second_ae.mono (fun p ht =>
      le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using
        realGaussianGammaJointProfile_norm_le M hM delta hN hCol p.1 p.2 ht))
  calc
    _ = MeasureTheory.integral (gaussianTensorMeasure.prod gammaHalfLine)
        (realGaussianGammaJointProfile M hM delta) := (integral_prod_symm _ hP).symm
    _ <= MeasureTheory.integral (gaussianTensorMeasure.prod gammaHalfLine)
        (realGaussianGammaJointEnvelope M hM n delta) := integral_mono_ae hP hQ hDom
    _ = MeasureTheory.integral gammaHalfLine (fun t =>
        MeasureTheory.integral gaussianTensorMeasure (fun x =>
          realGaussianGammaJointEnvelope M hM n delta (x, t))) := integral_prod_symm _ hQ
    _ = _ := realGaussianGammaJointEnvelope_total M hM n delta rho hNorm hGap

end PrimeFactorOscillations
