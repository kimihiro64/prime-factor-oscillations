/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasLogSpectral
import PrimeFactorOscillations.Helpers.NicolasPrimeProductCriterion
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock

/-!
# The spatial prime-product clock under RH

The exact exponential identity and the finite Nicolas logarithm expansion
locate the clock relative to theta on the square-root scale. The complete
canonical zero wave is retained; theta is not replaced by x at this precision.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

theorem nicolasPrimeProductClock_eq_theta_mul_exp {x : Real}
    (hx : 1 < Chebyshev.theta x) :
    nicolasPrimeProductClock x = Chebyshev.theta x *
      Real.exp (Real.log (Chebyshev.theta x) *
        (Real.exp (-nicolasLogMertensOscillation x) - 1)) := by
  have hThetaPos : 0 < Chebyshev.theta x := by linarith
  have hLogPos : 0 < Real.log (Chebyshev.theta x) := Real.log_pos hx
  have hM := nicolasMertensProduct_pos x
  have hf : 0 < nicolasFunction x := by
    unfold nicolasFunction
    positivity
  have hInv : Real.exp (-nicolasLogMertensOscillation x) = 1 / nicolasFunction x := by
    unfold nicolasLogMertensOscillation
    rw [Real.exp_neg, Real.exp_log hf, one_div]
  rw [nicolasPrimeProductClock_eq_theta_rpow hx, Real.rpow_def_of_pos hThetaPos, hInv]
  rw [show Real.log (Chebyshev.theta x) * (1 / nicolasFunction x) =
      Real.log (Chebyshev.theta x) +
        Real.log (Chebyshev.theta x) * (1 / nicolasFunction x - 1) by ring,
    Real.exp_add, Real.exp_log hThetaPos]


theorem eventually_abs_nicolasLog_scaled_error_le (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real =>
      abs (nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x) +
        (2 + nicolasZeroWave x)) <=
          nicolasLogSpectralConstant * Inv.inv (Real.log x)) atTop := by
  filter_upwards [eventually_nicolasLog_wave_uniform_error hRH,
    eventually_ge_atTop (2 : Real)] with x hError hx
  have hxPos : 0 < x := by linarith
  have hLog : 0 < Real.log x := Real.log_pos (by linarith)
  have hRoot : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
  have hProduct : 0 < x ^ (1 / 2 : Real) * Real.log x := mul_pos hRoot hLog
  have hScaled := mul_le_mul_of_nonneg_right hError hProduct.le
  calc
    _ = abs ((nicolasLogMertensOscillation x +
        (2 + nicolasZeroWave x) / (x ^ (1 / 2 : Real) * Real.log x)) *
          (x ^ (1 / 2 : Real) * Real.log x)) := by
      congr 1
      field_simp
    _ = abs (nicolasLogMertensOscillation x +
        (2 + nicolasZeroWave x) / (x ^ (1 / 2 : Real) * Real.log x)) *
          (x ^ (1 / 2 : Real) * Real.log x) := by
      rw [abs_mul, abs_of_pos hProduct]
    _ <= (nicolasLogSpectralConstant * x ^ (-(1 / 2 : Real)) *
        Inv.inv ((Real.log x) ^ 2)) * (x ^ (1 / 2 : Real) * Real.log x) := hScaled
    _ = _ := by
      rw [Real.rpow_neg hxPos.le]
      field_simp

theorem tendsto_nicolasLog_scaled_error (hRH : RiemannHypothesis) :
    Tendsto (fun x : Real =>
      nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x) +
        (2 + nicolasZeroWave x)) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hBound : Tendsto (fun x : Real => nicolasLogSpectralConstant * Inv.inv (Real.log x))
      atTop (nhds 0) := by
    simpa only [mul_zero, Pi.inv_apply] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul nicolasLogSpectralConstant
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hBound
  simpa only [Real.norm_eq_abs] using eventually_abs_nicolasLog_scaled_error_le hRH


theorem tendsto_nicolasLog_mul_log (hRH : RiemannHypothesis) :
    Tendsto (fun x : Real => nicolasLogMertensOscillation x * Real.log x)
      atTop (nhds 0) := by
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  let C := nicolasLogSpectralConstant + 2 + abs beta
  have hEnvelope : Filter.Eventually (fun x : Real =>
      norm (nicolasLogMertensOscillation x * Real.log x) <=
        C * x ^ (-(1 / 2 : Real))) atTop := by
    filter_upwards [eventually_nicolasHeight_domain hRH,
      eventually_abs_nicolasLog_scaled_error_le hRH] with x hx hZ
    have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
    have hx1 : 1 < x := by linarith
    have hxPos : 0 < x := by linarith
    have hExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
    have hL : 1 <= Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 <= x by linarith [Real.exp_pos 1])
      simpa only [Real.log_exp] using h
    have hLPos : 0 < Real.log x := by linarith
    have hRoot : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
    have hInv : Inv.inv (Real.log x) <= 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hL
    have hZCoeff : nicolasLogSpectralConstant * Inv.inv (Real.log x) <=
        nicolasLogSpectralConstant := by
      have h := mul_le_mul_of_nonneg_left hInv nicolasLogSpectralConstant_pos.le
      simpa only [mul_one] using h
    have hZMax := hZ.trans hZCoeff
    have hWave := abs_nicolasZeroWave_le hRH hx1
    have hW : abs (2 + nicolasZeroWave x) <= 2 + abs beta := by
      have h := abs_add_le (2 : Real) (nicolasZeroWave x)
      norm_num at h
      have hBeta : beta <= abs beta := le_abs_self beta
      dsimp [beta] at hBeta
      linarith only [h, hWave, hBeta]
    have hAbs : abs (nicolasLogMertensOscillation x *
        (x ^ (1 / 2 : Real) * Real.log x)) <= C := by
      have hTriangle := abs_sub_le
        (nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x) +
          (2 + nicolasZeroWave x)) 0 (2 + nicolasZeroWave x)
      simp only [sub_zero, zero_sub, abs_neg, add_sub_cancel_right] at hTriangle
      dsimp [C]
      linarith only [hTriangle, hZMax, hW]
    rw [Real.norm_eq_abs]
    calc
      _ = abs ((nicolasLogMertensOscillation x *
          (x ^ (1 / 2 : Real) * Real.log x)) / x ^ (1 / 2 : Real)) := by
        congr 1
        field_simp
      _ = abs (nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x)) *
          Inv.inv (x ^ (1 / 2 : Real)) := by
        rw [abs_div, abs_of_pos hRoot, div_eq_mul_inv]
      _ <= C * Inv.inv (x ^ (1 / 2 : Real)) :=
        mul_le_mul_of_nonneg_right hAbs (inv_nonneg.mpr hRoot.le)
      _ = _ := by rw [Real.rpow_neg hxPos.le]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hEnvelope
  simpa only [mul_zero] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 2)).const_mul C

theorem tendsto_nicolasLog_zero (hRH : RiemannHypothesis) :
    Tendsto nicolasLogMertensOscillation atTop (nhds 0) := by
  have h := (tendsto_nicolasLog_mul_log hRH).div_atTop Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hLog : 0 < Real.log x := Real.log_pos (by linarith)
  field_simp


theorem tendsto_nicolasPrimeProductClock_normalized_error (hRH : RiemannHypothesis) :
    Tendsto (fun x : Real =>
      (nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) -
        (2 + nicolasZeroWave x)) atTop (nhds 0) := by
  let u : Real -> Real := fun x => -nicolasLogMertensOscillation x
  let v : Real -> Real := fun x => Real.log (Chebyshev.theta x) * (Real.exp (u x) - 1)
  let A : Real -> Real := fun x => u x * (x ^ (1 / 2 : Real) * Real.log x)
  let P : Real -> Real := fun x =>
    (Chebyshev.theta x / x) * (Real.log (Chebyshev.theta x) / Real.log x) *
      ((Real.exp (u x) - 1) / u x) * ((Real.exp (v x) - 1) / v x)
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  let B := nicolasLogSpectralConstant + 2 + abs beta
  have hSelf : Tendsto (fun x : Real => x) atTop atTop := tendsto_id
  have hTheta : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (hSelf.eventually_ne_atTop 0)).mp
      primeProfile_theta_isEquivalent_id
  have hThetaLog : Tendsto (fun x : Real => Real.log (Chebyshev.theta x) / Real.log x)
      atTop (nhds 1) := by
    have hLogRatio : Tendsto (fun x : Real => Real.log (Chebyshev.theta x / x))
        atTop (nhds 0) := by
      simpa only [Real.log_one, Function.comp_def] using
        (Real.continuousAt_log (by norm_num : Not ((1 : Real) = 0))).tendsto.comp hTheta
    have hSmall := hLogRatio.div_atTop Real.tendsto_log_atTop
    have hLimit : Tendsto (fun x : Real => 1 + Real.log (Chebyshev.theta x / x) / Real.log x)
        atTop (nhds 1) := by simpa only [add_zero] using hSmall.const_add 1
    apply hLimit.congr'
    filter_upwards [eventually_nicolasHeight_domain hRH] with x hx
    have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
    have hxPos : 0 < x := by linarith
    have hThetaPos : 0 < Chebyshev.theta x := by
      have h := one_lt_chebyshevTheta_of_three_le (by linarith : 3 <= x)
      linarith
    have hLog : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Real.log_div hThetaPos.ne' hxPos.ne']
    field_simp
    ring
  have hu : Tendsto u atTop (nhds 0) := by
    simpa only [u, neg_zero] using (tendsto_nicolasLog_zero hRH).neg
  have huLog : Tendsto (fun x => u x * Real.log x) atTop (nhds 0) := by
    simpa only [u, neg_mul, neg_zero] using (tendsto_nicolasLog_mul_log hRH).neg
  have huPos : Filter.Eventually (fun x => 0 < u x) atTop := by
    filter_upwards [riemannHypothesis_iff_eventually_nicolasLog_neg.mp hRH] with x hx
    exact neg_pos.mpr hx
  have huNe : Filter.Eventually (fun x => Not (u x = 0)) atTop :=
    huPos.mono (fun _ hx => hx.ne')
  have hExpQuotient (w : Real -> Real) (hw : Tendsto w atTop (nhds 0))
      (hwNe : Filter.Eventually (fun x => Not (w x = 0)) atTop) :
      Tendsto (fun x => (Real.exp (w x) - 1) / w x) atTop (nhds 1) := by
    have hWithin : Tendsto w atTop (nhdsWithin 0 (Set.compl ({0} : Set Real))) := by
      have hPrincipal : Tendsto w atTop (Filter.principal (Set.compl ({0} : Set Real))) := by
        apply Filter.tendsto_principal.mpr
        filter_upwards [hwNe] with x hx
        exact hx
      simpa [nhdsWithin] using hw.inf hPrincipal
    have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hWithin
    simp only [zero_add, Real.exp_zero, smul_eq_mul] at h
    convert h using 1
    funext x
    dsimp only [Function.comp_apply]
    ring
  have hEU := hExpQuotient u hu huNe
  have hv : Tendsto v atTop (nhds 0) := by
    have hLimit : Tendsto (fun x =>
        (Real.log (Chebyshev.theta x) / Real.log x) *
          ((Real.exp (u x) - 1) / u x) * (u x * Real.log x)) atTop (nhds 0) := by
      simpa only [mul_one, mul_zero] using (hThetaLog.mul hEU).mul huLog
    apply hLimit.congr'
    filter_upwards [eventually_nicolasHeight_domain hRH, huNe] with x hx hune
    have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
    have hLog : 0 < Real.log x := Real.log_pos (by linarith)
    dsimp only [v]
    field_simp
  have hvNe : Filter.Eventually (fun x => Not (v x = 0)) atTop := by
    filter_upwards [eventually_nicolasHeight_domain hRH, huPos] with x hx hux
    have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
    have ht := one_lt_chebyshevTheta_of_three_le (by linarith : 3 <= x)
    have he : 0 < Real.exp (u x) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hux)
    exact (mul_pos (Real.log_pos ht) he).ne'
  have hEV := hExpQuotient v hv hvNe
  have hP : Tendsto P atTop (nhds 1) := by
    simpa only [P, mul_one] using ((hTheta.mul hThetaLog).mul hEU).mul hEV
  have hAmp : Filter.Eventually (fun x => abs (A x) <= B) atTop := by
    filter_upwards [eventually_nicolasHeight_domain hRH,
      eventually_abs_nicolasLog_scaled_error_le hRH] with x hx hZ
    have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
    have hx1 : 1 < x := by linarith
    have hExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
    have hL : 1 <= Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 <= x by linarith [Real.exp_pos 1])
      simpa only [Real.log_exp] using h
    have hInv : Inv.inv (Real.log x) <= 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hL
    have hZCoeff : nicolasLogSpectralConstant * Inv.inv (Real.log x) <=
        nicolasLogSpectralConstant := by
      have h := mul_le_mul_of_nonneg_left hInv nicolasLogSpectralConstant_pos.le
      simpa only [mul_one] using h
    have hZMax := hZ.trans hZCoeff
    have hWave := abs_nicolasZeroWave_le hRH hx1
    have hW := abs_add_le (2 : Real) (nicolasZeroWave x)
    norm_num at hW
    have hBeta : beta <= abs beta := le_abs_self beta
    have hTriangle := abs_sub_le
      (nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x) +
        (2 + nicolasZeroWave x)) 0 (2 + nicolasZeroWave x)
    simp only [sub_zero, zero_sub, abs_neg, add_sub_cancel_right] at hTriangle
    dsimp [A, u, B]
    rw [neg_mul, abs_neg]
    dsimp [beta] at hBeta
    nlinarith only [hTriangle, hZMax, hWave, hW, hBeta]
  have hProdError : Tendsto (fun x => (P x - 1) * A x) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hBound : Tendsto (fun x => B * norm (P x - 1)) atTop (nhds 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using ((hP.sub_const 1).norm).const_mul B
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hBound
    filter_upwards [hAmp] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left hx (abs_nonneg (P x - 1))
    nlinarith only [h]
  have hAmpError : Tendsto (fun x => A x - (2 + nicolasZeroWave x)) atTop (nhds 0) := by
    have hFun : (fun x => A x - (2 + nicolasZeroWave x)) =
        (fun x => -(nicolasLogMertensOscillation x * (x ^ (1 / 2 : Real) * Real.log x) +
          (2 + nicolasZeroWave x))) := by
      funext x
      dsimp [A, u]
      ring
    rw [hFun]
    simpa only [neg_zero] using (tendsto_nicolasLog_scaled_error hRH).neg
  have hExact (x : Real) (hx : max 4 (2 * Real.exp 1) <= x)
      (hune : Not (u x = 0)) (hvne : Not (v x = 0)) :
      (nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) =
        P x * A x := by
    have hx4 : 4 <= x := (le_max_left _ _).trans hx
    have hxPos : 0 < x := by linarith
    have hThetaOne := one_lt_chebyshevTheta_of_three_le (by linarith : 3 <= x)
    have hLog : 0 < Real.log x := Real.log_pos (by linarith)
    have hRoot : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
    have hRootSq : (x ^ (1 / 2 : Real)) ^ (2 : Nat) = x := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
      norm_num
    rw [nicolasPrimeProductClock_eq_theta_mul_exp hThetaOne]
    change (Chebyshev.theta x * Real.exp (v x) - Chebyshev.theta x) /
      x ^ (1 / 2 : Real) = P x * A x
    dsimp only [P, A]
    field_simp
    dsimp only [v]
    ring_nf
    all_goals rw [hRootSq]
  have hFinal : Tendsto (fun x =>
      (P x - 1) * A x + (A x - (2 + nicolasZeroWave x))) atTop (nhds 0) := by
    simpa only [add_zero] using hProdError.add hAmpError
  apply hFinal.congr'
  filter_upwards [eventually_nicolasHeight_domain hRH, huNe, hvNe] with x hx hune hvne
  rw [hExact x hx.1 hune hvne]
  ring

end PrimeFactorOscillations
