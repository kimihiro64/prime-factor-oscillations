/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Generalizes the maintained Robin1984 endpoint reweighting proof,
ported from bfa72aec0c25c8ee29cefe4449d778ff30412bee (Apache-2.0).
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedEndpointArithmetic
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedEndpointZeros
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripExplicit
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripRemainder

/-!
# Complete weighted explicit formula at the endpoint under a strip bound

A common upper bound Re(rho) <= b < 1 makes the reweighted n = 2 majorant
integrable. Absolute summability justifies the complete zero-sum interchange
and gives the n = 1 arithmetic identity with its full trivial-zero correction.
The strip bound remains an explicit hypothesis; this file does not prove QRH.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Robin1984
open Complex MeasureTheory Set

theorem summable_robinZeroKernel_div_rho_strip
    {b : Real} (hb : b < 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= b)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) := by
  exact (summable_robinXiZeroWeight.mul_right (robinStripKernelMajorant b n x)).of_norm_bounded
    (fun p => norm_robinZeroKernel_div_rho_le_strip hn
      (riemannXiDivisorZeroValue_ne_zero p) (hUpper p) hb.le hx)

theorem norm_robinEndpointZeroAtom_le_strip
    {rho : Complex} (hRho : Not (rho = 0)) {b : Real}
    (hRe : rho.re <= b) (hb : b < 1) {t : Real} (ht : 1 < t) :
    norm ((robinEndpointReweightDerivative t : Complex) * (robinZeroKernel 2 rho t / rho)) <=
      (Inv.inv (norm rho))^2 * robinStripKernelMajorant b 2 t := by
  have hDerivative := robinEndpointReweightDerivative_bounds ht
  have hKernel := norm_robinZeroKernel_div_rho_le_strip
    (n := 2) (by norm_num) hRho hRe hb.le ht
  calc
    _ = robinEndpointReweightDerivative t * norm (robinZeroKernel 2 rho t / rho) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDerivative.1]
    _ <= 1 * norm (robinZeroKernel 2 rho t / rho) :=
      mul_le_mul_of_nonneg_right hDerivative.2 (norm_nonneg _)
    _ <= _ := by simpa only [one_mul] using hKernel

theorem summable_integral_norm_robinEndpointZeroAtoms_strip
    {b : Real} (hb : b < 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= b) {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((robinEndpointReweightDerivative t : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)))) := by
  have hM := integrableOn_robinStripKernelMajorant_two hb hx
  have hMajor (p : RiemannXiDivisorZeroIndex) :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((robinEndpointReweightDerivative t : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p))) <=
      (Inv.inv (norm (riemannXiDivisorZeroValue p)))^2 *
        integral (volume.restrict (Ioi x)) (robinStripKernelMajorant b 2) := by
    have hRe := hUpper p
    have hInt := integrableOn_robinEndpointZeroAtom hx (show (riemannXiDivisorZeroValue p).re < 1 by linarith)
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p)))^2 * robinStripKernelMajorant b 2 t) := by
        apply integral_mono_ae hInt.norm (hM.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_robinEndpointZeroAtom_le_strip (riemannXiDivisorZeroValue_ne_zero p) hRe hb (lt_trans hx ht)
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg _)) hMajor
    (summable_robinXiZeroWeight.mul_right _)

theorem robin_complete_zero_sum_one_reweight_strip
    {b : Real} (hb : b < 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= b) {x : Real} (hx : 1 < x) :
    And (IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)) (Ioi x))
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) =
        (robinEndpointReweight x : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
            robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p))) := by
  let := countable_robinXiDivisorZeroIndex
  let Z (p : RiemannXiDivisorZeroIndex) (t : Real) : Complex :=
    (robinEndpointReweightDerivative t : Complex) *
      (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)
  have hInt (p : RiemannXiDivisorZeroIndex) : IntegrableOn (Z p) (Ioi x) := by
    have hRe := hUpper p
    exact integrableOn_robinEndpointZeroAtom hx (by linarith)
  have hNorm : Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (fun t : Real => norm (Z p t))) :=
    summable_integral_norm_robinEndpointZeroAtoms_strip hb hUpper hx
  have hSumInt : Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (Z p)) :=
    hNorm.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  have hSeries := integrable_complex_series_of_integral_norm hInt hNorm
  have hWholeInt : IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)) (Ioi x) := by
    apply IntegrableOn.congr_fun hSeries _ measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    rw [tsum_mul_left]
  have hAtom (p : RiemannXiDivisorZeroIndex) :
      robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p =
        (robinEndpointReweight x : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p) := by
    have hRe := hUpper p
    have hRaw := (robinZeroKernel_one_reweight hx (show (riemannXiDivisorZeroValue p).re < 1 by linarith)).2
    rw [hRaw, add_div, mul_div_assoc]
    congr 1
    rw [<- integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    ring
  refine And.intro hWholeInt ?_
  calc
    _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
        (robinEndpointReweight x : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p)) := tsum_congr hAtom
    _ = (robinEndpointReweight x : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          tsum (fun p : RiemannXiDivisorZeroIndex => integral (volume.restrict (Ioi x)) (Z p)) := by
      rw [((summable_robinZeroKernel_div_rho_strip hb hUpper (by norm_num : 2 <= (2 : Nat)) hx).mul_left
        (robinEndpointReweight x : Complex)).tsum_add hSumInt, tsum_mul_left]
    _ = _ := by
      rw [integral_tsum_of_summable_integral_norm hInt hNorm]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [Z]
      rw [tsum_mul_left]

theorem robinPsiWeightedErrorIntegral_one_eq_zero_sum_correction_strip
    {b : Real} (hb : b < 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= b) {x : Real} (hx : 2 <= x) :
    (robinPsiWeightedErrorIntegral 1 x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
          (robinTrivialZeroCorrection 1 x : Complex) := by
  have hxOne : 1 < x := by linarith
  have hUpperOne : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1 := fun p => le_trans (hUpper p) hb.le
  let Z (t : Real) : Complex := tsum (fun p : RiemannXiDivisorZeroIndex =>
    robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)
  have hJ := robinPsiWeightedErrorIntegral_one_reweight hx
  have hC := robinTrivialZeroCorrection_one_reweight hx
  have hZ := robin_complete_zero_sum_one_reweight_strip hb hUpper hxOne
  have hInside : integral (volume.restrict (Ioi x)) (fun t : Real =>
      (robinEndpointReweightDerivative t : Complex) * (robinPsiWeightedErrorIntegral 2 t : Complex)) =
      -integral (volume.restrict (Ioi x)) (fun t : Real =>
        (robinEndpointReweightDerivative t : Complex) * Z t) -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * (robinTrivialZeroCorrection 2 t : Complex)) := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          -((robinEndpointReweightDerivative t : Complex) * Z t) -
            (robinEndpointReweightDerivative t : Complex) * (robinTrivialZeroCorrection 2 t : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [robinPsiWeightedErrorIntegral_eq_zero_sum_correction_strip hUpperOne
          (by norm_num : 2 <= (2 : Nat)) (le_trans hx ht.le)]
        dsimp only [Z]
        ring
      _ = _ := by
        have hNeg : IntegrableOn (fun t : Real =>
            -((robinEndpointReweightDerivative t : Complex) * Z t)) (Ioi x) := hZ.1.neg
        rw [integral_sub hNeg hC.1, integral_neg]
  rw [hJ.2, robinPsiWeightedErrorIntegral_eq_zero_sum_correction_strip hUpperOne
    (by norm_num : 2 <= (2 : Nat)) hx, hInside, hZ.2, hC.2]
  dsimp only [Z]
  ring


end Robin1984
