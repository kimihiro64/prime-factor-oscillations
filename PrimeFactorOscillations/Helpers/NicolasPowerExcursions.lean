/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasTiltedIntegral

/-!
# Zero-dependent signed integral excursions

The negative Omega argument below adapts the audited rightmost-ray proof
from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee,
NicolasLandau/NicolasLandauRightmostRay.lean, to an arbitrary admissible
exponent. All analytic inputs and the exact pole contradiction are retained.
A smaller exponent amplifies the negative Omega bound to every amplitude.
The existing positive-excursion theorem already has that exponent scope.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter MeasureTheory ProbabilityTheory Set Robin1984
open scoped ENNReal Topology

theorem nicolasJ_omegaMinus_of_zero_at_exponent
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)) := by
  choose rhoMax hMaxZero hMaxHalf hMaxOne hMaxIm hRay using
    exists_rightmost_horizontal_riemannZeta_zero hZero hHalf hOne
  have hRe : rho.re <= rhoMax.re := by
    apply le_of_not_gt
    intro hlt
    have hv : 0 < rho.re - rhoMax.re := sub_pos.mpr hlt
    have hShift : rhoMax + ((rho.re - rhoMax.re : Real) : Complex) = rho := by
      apply Complex.ext
      . simp only [Complex.add_re, Complex.ofReal_re]
        ring
      . simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hMaxIm
    apply hRay (rho.re - rhoMax.re) hv
    rw [hShift]
    exact hZero
  have hbPos : 0 < b := by linarith
  have hbLower : 1 - rhoMax.re < b := by linarith
  by_contra hNot
  choose X hX hPos hAnalytic using
    exists_nicolasLandauComplexMGF_analytic_halfPlane_of_not_omegaMinus
      hbPos hbHalf hNot
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let MGF : Real -> Complex := fun eps =>
    complexMGF (fun x : Real => Real.log x)
      (nicolasLandauPositiveMeasure X b)
      (nicolasRightmostRayPoint rhoMax eps)
  let P : Real -> Complex := fun eps =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rhoMax eps)
  have hPointRe : (nicolasRightmostRayPoint rhoMax 0).re = 1 - rhoMax.re := by
    unfold nicolasRightmostRayPoint
    simp
  have hMGFAnalytic : AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x) (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rhoMax 0) := by
    apply hAnalytic
    rw [hPointRe]
    exact hbLower
  let MGF0 : Complex := complexMGF (fun x : Real => Real.log x)
    (nicolasLandauPositiveMeasure X b) (nicolasRightmostRayPoint rhoMax 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rhoMax) l
      (nhds (nicolasRightmostRayPoint rhoMax 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rhoMax) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hMGF : Tendsto MGF l (nhds MGF0) := by
    simpa [MGF, MGF0, Function.comp_def] using hMGFAnalytic.continuousAt.tendsto.comp hInner
  have hEq : Filter.Eventually (fun eps : Real => MGF eps = P eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    dsimp [MGF, P]
    exact nicolasLandauComplexMGF_eq_continuationFilled_rightmostRay
      hX hbPos hbHalf hPos hMaxZero hMaxHalf hMaxOne hbLower hRay (mem_Ioi.mp hEps)
  have hPNormFinite : Tendsto (fun eps : Real => norm (P eps)) l (nhds (norm MGF0)) := by
    apply hMGF.norm.congr'
    filter_upwards [hEq] with eps hAt
    rw [hAt]
  have hPNormTop : Tendsto (fun eps : Real => norm (P eps)) l atTop := by
    simpa [l, P] using
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        hX hMaxZero hMaxHalf hMaxOne hRay
  exact not_tendsto_nhds_of_tendsto_atTop hPNormTop (norm MGF0) hPNormFinite

theorem nicolasJ_arbitrary_negative_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    forall X A : Real, exists x : Real,
      max X 3 < x /\ A * x ^ (-b) < -nicolasJ x := by
  let b0 : Real := ((1 - rho.re) + b) / 2
  have h0Lower : 1 - rho.re < b0 := by dsimp [b0]; linarith
  have h0b : b0 < b := by dsimp [b0]; linarith
  have h0Half : b0 <= 1 / 2 := by linarith
  have hOmega := nicolasJ_omegaMinus_of_zero_at_exponent hZero hHalf hOne h0Lower h0Half
  choose c hc hLarge using hOmega
  intro X A
  have hGrowth := (tendsto_rpow_atTop (show 0 < b - b0 by linarith)).eventually_gt_atTop (A / c)
  choose Y hY using eventually_atTop.mp hGrowth
  choose x hx hJ using hLarge (max (max X 3 + 1) Y)
  change c * x ^ (-b0) <= -nicolasJ x at hJ
  have hxLarge : max X 3 < x := by
    have h := (le_max_left (max X 3 + 1) Y).trans hx
    linarith
  have hx3 : 3 < x := (le_max_right X 3).trans_lt hxLarge
  have hx0 : 0 < x := by linarith
  have hScale := mul_lt_mul_of_pos_left (hY x ((le_max_right _ _).trans hx)) hc
  have hCancel : c * (A / c) = A := by field_simp
  rw [hCancel] at hScale
  have hMultiply := mul_lt_mul_of_pos_right hScale (Real.rpow_pos_of_pos hx0 (-b))
  have hIdentity : (c * x ^ (b - b0)) * x ^ (-b) = c * x ^ (-b0) := by
    rw [mul_assoc, <- Real.rpow_add hx0]
    have he : b - b0 + -b = -b0 := by ring
    rw [he]
  rw [hIdentity] at hMultiply
  exact Exists.intro x (And.intro hxLarge (hMultiply.trans_le hJ))

theorem nicolasK_two_sided_power_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    forall X A : Real,
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasK x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasK x) := by
  intro X A
  constructor
  . choose x hx hJ using
      nicolasJ_arbitrary_positive_excursions_of_zero hZero hHalf hOne hLower hbHalf X (A + 8)
    have hx3 : 3 <= x := ((le_max_right X 3).trans_lt hx).le
    have hx1 : 1 <= x := by linarith
    have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
      (Ioi_subset_Ioi (show 2 <= x by linarith))
    have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set (Ioi_subset_Ioi hx3)
    have hId := nicolasJ_eq_K_add_primePowerTail hKInt hJInt
    have hP : nicolasPrimePowerTail x <= 8 * x ^ (-(1 / 2 : Real)) := by
      simpa only [nicolasPrimePowerTail, nicolasTailKernel] using
        (Chebyshev.primePowerLogTail_bounds hx3).2
    have hPower := Real.rpow_le_rpow_of_exponent_le hx1
      (show -(1 / 2 : Real) <= -b by linarith)
    have hPaid : nicolasPrimePowerTail x <= 8 * x ^ (-b) :=
      hP.trans (mul_le_mul_of_nonneg_left hPower (by norm_num))
    refine Exists.intro x (And.intro hx ?_)
    nlinarith only [hJ, hId, hPaid]
  . choose x hx hJ using
      nicolasJ_arbitrary_negative_excursions_of_zero hZero hHalf hOne hLower hbHalf X A
    have hx3 : 3 <= x := ((le_max_right X 3).trans_lt hx).le
    have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
      (Ioi_subset_Ioi (show 2 <= x by linarith))
    have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set (Ioi_subset_Ioi hx3)
    have hK := nicolasK_le_J (show 1 <= x by linarith) hKInt hJInt
    exact Exists.intro x (And.intro hx (by linarith only [hJ, hK]))

theorem nicolasTiltedIntegral_two_sided_power_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (z : Real) (hz : 0 < z) :
    forall X A : Real,
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasTiltedIntegral z x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasTiltedIntegral z x) := by
  let C := nicolasTiltedIntegralErrorConstant z
  have hC : 0 <= C := nicolasTiltedIntegralErrorConstant_nonneg hz.le
  have hError (x : Real) (hx : 3 <= x) :
      |nicolasTiltedIntegral z x - z * nicolasK x| <= C * x ^ (-b) := by
    have hx0 : 0 < x := by linarith
    have hx1 : 1 <= x := by linarith
    have hlog : 1 <= Real.log x :=
      ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hx)).le
    have hLogBound : C / (x * Real.log x) <= C / x := by
      calc
        _ = (C / x) / Real.log x := by ring
        _ <= (C / x) / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
        _ = _ := div_one _
    have hPower := Real.rpow_le_rpow_of_exponent_le hx1
      (show -(1 : Real) <= -b by linarith)
    rw [Real.rpow_neg_one] at hPower
    have hPowerBound : C / x <= C * x ^ (-b) := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hPower hC
    exact (nicolasTiltedIntegral_error hz.le hx).trans (hLogBound.trans hPowerBound)
  intro X A
  let B : Real := (A + C) / z
  have hCancel : z * B = A + C := by dsimp [B]; field_simp
  have hSupply := nicolasK_two_sided_power_excursions_of_zero
    hZero hHalf hOne hLower hbHalf X B
  constructor
  . choose x hx hK using hSupply.1
    have he := (abs_le.mp (hError x ((le_max_right X 3).trans_lt hx).le)).1
    have hScale := mul_lt_mul_of_pos_left hK hz
    have hProduct : z * (B * x ^ (-b)) = (A + C) * x ^ (-b) := by
      rw [<- mul_assoc, hCancel]
    rw [hProduct] at hScale
    exact Exists.intro x (And.intro hx (by nlinarith only [he, hScale]))
  . choose x hx hK using hSupply.2
    have he := (abs_le.mp (hError x ((le_max_right X 3).trans_lt hx).le)).2
    have hScale := mul_lt_mul_of_pos_left hK hz
    have hProduct : z * (B * x ^ (-b)) = (A + C) * x ^ (-b) := by
      rw [<- mul_assoc, hCancel]
    rw [hProduct] at hScale
    exact Exists.intro x (And.intro hx (by nlinarith only [he, hScale]))

end PrimeFactorOscillations
