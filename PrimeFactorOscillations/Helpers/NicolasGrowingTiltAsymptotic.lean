/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasGrowingTilt
import PrimeFactorOscillations.Helpers.PrimeReciprocalSquareTail

/-!
# The sharp square-root growing-tilt correction

The PNT prime-square tail and a uniform cubic remainder yield coefficient
-c/2 without RH. The proof retains the real cutoff and its natural floor;
no fixed-tilt estimate is applied outside a uniform range.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

private theorem growing_tendsto_natFloor :
    Tendsto (fun x : Real => Nat.floor x) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (N : Real)] with x hx
  exact Nat.le_floor hx

private theorem growing_floor_ratio :
    Tendsto (fun x : Real => (Nat.floor x : Real) / x) atTop (nhds 1) := by
  have hInv : Tendsto (fun x : Real => 1 / x) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x) atTop (nhds 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun x : Real => 1 - 1 / x) atTop (nhds 1) from by
      simpa only [sub_zero] using tendsto_const_nhds.sub hInv)
    tendsto_const_nhds
  . filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := by linarith
    have hf := Nat.lt_floor_add_one x
    have h := div_le_div_of_nonneg_right
      (show x - 1 <= (Nat.floor x : Real) by linarith) hx0.le
    have hid : (x - 1) / x = 1 - 1 / x := by field_simp
    rwa [hid] at h
  . filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := by linarith
    exact (div_le_one hx0).mpr (Nat.floor_le hx0.le)

private theorem growing_log_floor_ratio :
    Tendsto (fun x : Real => Real.log (Nat.floor x : Real) / Real.log x)
      atTop (nhds 1) := by
  have hLog := (Real.continuousAt_log (by norm_num : Not ((1 : Real) = 0))).tendsto.comp
    growing_floor_ratio
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hSmall := hLog.mul hInv
  have hTotal := (tendsto_const_nhds (x := (1 : Real))).add hSmall
  have hT : Tendsto (fun x : Real => 1 +
      Real.log ((Nat.floor x : Real) / x) / Real.log x) atTop (nhds 1) := by
    simpa only [Real.log_one, zero_mul, add_zero, div_eq_mul_inv, Function.comp_def] using hTotal
  apply hT.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hn0 : (0 : Real) < Nat.floor x := by exact_mod_cast (show 0 < Nat.floor x by omega)
  have hx0 : 0 < x := by linarith
  have hl0 : Not (Real.log x = 0) := (Real.log_pos (by linarith)).ne'
  rw [Real.log_div hn0.ne' hx0.ne']
  field_simp
  <;> ring

theorem tendsto_primeProfileQuadraticTail_floor_scaled :
    Tendsto (fun x : Real => primeProfileQuadraticTail (Nat.floor x) *
      (x * Real.log x)) atTop (nhds 1) := by
  have hSq := tendsto_primeProfileQuadraticTail_scaled.comp growing_tendsto_natFloor
  have hInvFloor : Tendsto (fun x : Real => 1 / ((Nat.floor x : Real) / x)) atTop (nhds 1) := by
    simpa only [div_one, Pi.div_def] using (tendsto_const_nhds (x := (1 : Real))).div
      growing_floor_ratio (by norm_num)
  have hInvLog : Tendsto (fun x : Real => 1 / (Real.log (Nat.floor x : Real) / Real.log x))
      atTop (nhds 1) := by
    simpa only [div_one, Pi.div_def] using (tendsto_const_nhds (x := (1 : Real))).div
      growing_log_floor_ratio (by norm_num)
  have hAll := (hSq.mul hInvFloor).mul hInvLog
  have ht : Tendsto (fun x : Real =>
      (primeProfileQuadraticTail (Nat.floor x) *
        ((Nat.floor x : Real) * Real.log (Nat.floor x : Real))) *
        Inv.inv ((Nat.floor x : Real) / x) *
        Inv.inv (Real.log (Nat.floor x : Real) / Real.log x)) atTop (nhds 1) := by
    simpa only [Function.comp_def, one_div, mul_one] using hAll
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hn1 : (1 : Real) < Nat.floor x := by exact_mod_cast (show 1 < Nat.floor x by omega)
  have hn0 : Not ((Nat.floor x : Real) = 0) := (zero_lt_one.trans hn1).ne'
  have hln : Not (Real.log (Nat.floor x : Real) = 0) := (Real.log_pos hn1).ne'
  have hx0 : Not (x = 0) := by linarith
  have hlx : Not (Real.log x = 0) := (Real.log_pos (by linarith)).ne'
  field_simp

theorem tendsto_growing_primeProfile_tail_scaled (c : Real) (hc : 0 < c) :
    Tendsto (fun x : Real =>
      (Real.log (primeProfile ((c * Real.sqrt x : Real) : Complex)).re -
       Real.log (primePrefixProfile (Nat.floor x) ((c * Real.sqrt x : Real) : Complex)).re) *
        Real.log x / c) atTop (nhds (-c / 2)) := by
  let z : Real -> Real := fun x => c * Real.sqrt x
  let T : Real -> Real := fun x =>
    Real.log (primeProfile ((z x : Real) : Complex)).re -
      Real.log (primePrefixProfile (Nat.floor x) ((z x : Real) : Complex)).re
  let E : Real -> Real := fun x => T x +
    ((z x) ^ (2 : Nat) - z x) / 2 * primeProfileQuadraticTail (Nat.floor x)
  have hInv : Tendsto (fun x : Real => 1 / x) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x) atTop (nhds 0))
  have hLogRoot : Tendsto (fun x : Real => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hMajor : Tendsto (fun x : Real =>
      (8 / 3 : Real) * (c ^ (2 : Nat) + 1 / x) * (Real.log x / Real.sqrt x))
      atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using
      ((tendsto_const_nhds.add hInv).const_mul (8 / 3 : Real)).mul hLogRoot
  have hE : Tendsto (fun x : Real => E x * Real.log x / c) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x : Real =>
      (8 / 3 : Real) * (c ^ (2 : Nat) + 1 / x) * (Real.log x / Real.sqrt x)) ?_ hMajor
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hN : 1 <= Nat.floor x := Nat.le_floor (by norm_num; linarith)
    have hNr : (0 : Real) < Nat.floor x := by exact_mod_cast (show 0 < Nat.floor x by omega)
    have hFloor := Nat.lt_floor_add_one x
    have hHalf : x / 2 <= (Nat.floor x : Real) := by linarith
    have hInvSq : 1 / (Nat.floor x : Real) ^ (2 : Nat) <= 4 / x ^ (2 : Nat) := by
      calc
        _ <= 1 / (x ^ (2 : Nat) / 4) := one_div_le_one_div_of_le
          (by positivity) (by nlinarith)
        _ = _ := by field_simp
    have hb := primeProfile_log_tail_quadratic_bound (Nat.floor x) hN (z x)
      (mul_nonneg hc.le (Real.sqrt_nonneg x))
    change abs (E x) <= _ at hb
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hc, abs_of_pos hl]
    calc
      _ <= (2 * ((z x) ^ (3 : Nat) + z x) /
          (3 * (Nat.floor x : Real) ^ (2 : Nat))) * Real.log x / c :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hl.le) hc.le
      _ <= (8 * ((z x) ^ (3 : Nat) + z x) / (3 * x ^ (2 : Nat))) * Real.log x / c := by
        apply div_le_div_of_nonneg_right _ hc.le
        apply mul_le_mul_of_nonneg_right _ hl.le
        have hm := mul_le_mul_of_nonneg_left hInvSq
          (show 0 <= 2 * ((z x) ^ (3 : Nat) + z x) / 3 by dsimp [z]; positivity)
        convert hm using 1 <;> ring
      _ = _ := by
        let s : Real := Real.sqrt x
        have hs : 0 < s := Real.sqrt_pos.mpr hx0
        have hsq : s ^ (2 : Nat) = x := Real.sq_sqrt hx0.le
        change (8 * ((c * s) ^ (3 : Nat) + c * s) / (3 * x ^ (2 : Nat))) *
          Real.log x / c = (8 / 3 : Real) * (c ^ (2 : Nat) + 1 / x) * (Real.log x / s)
        rw [<- hsq]
        field_simp
        <;> ring
  have hRootInv : Tendsto (fun x : Real => 1 / Real.sqrt x) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hMain : Tendsto (fun x : Real =>
      ((z x) ^ (2 : Nat) - z x) / 2 * primeProfileQuadraticTail (Nat.floor x) *
        Real.log x / c) atTop (nhds (c / 2)) := by
    have hCoef : Tendsto (fun x : Real => (c - 1 / Real.sqrt x) / 2) atTop (nhds (c / 2)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hRootInv).div_const 2
    have ht := hCoef.mul tendsto_primeProfileQuadraticTail_floor_scaled
    apply (show Tendsto (fun x : Real => (c - 1 / Real.sqrt x) / 2 *
      (primeProfileQuadraticTail (Nat.floor x) * (x * Real.log x))) atTop (nhds (c / 2))
        from by simpa only [mul_one] using ht).congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    let s : Real := Real.sqrt x
    have hs : 0 < s := Real.sqrt_pos.mpr hx
    have hsq : s ^ (2 : Nat) = x := Real.sq_sqrt hx.le
    change (c - 1 / s) / 2 * (primeProfileQuadraticTail (Nat.floor x) * (x * Real.log x)) =
      ((c * s) ^ (2 : Nat) - c * s) / 2 * primeProfileQuadraticTail (Nat.floor x) * Real.log x / c
    rw [<- hsq]
    field_simp
    <;> ring
  have h := hE.sub hMain
  apply (show Tendsto (fun x : Real =>
      E x * Real.log x / c -
        ((z x) ^ (2 : Nat) - z x) / 2 * primeProfileQuadraticTail (Nat.floor x) *
          Real.log x / c) atTop (nhds (-c / 2)) from by
      simpa only [zero_sub, neg_div] using h).congr'
  filter_upwards [] with x
  dsimp only [E, T, z]
  ring

/-- The exact growing-tilt correction has coefficient -c/2 at the
sqrt(x) log(x) normalization, without an RH assumption. -/
theorem tendsto_nicolasGrowingTilt_correction (c : Real) (hc : 0 < c) :
    Tendsto (fun x : Real =>
      (nicolasTiltedLog (c * Real.sqrt x) x / (c * Real.sqrt x) -
        nicolasLogMertensOscillation x) * (Real.sqrt x * Real.log x))
      atTop (nhds (-c / 2)) := by
  have hTheta : Filter.Eventually (fun x : Real => 1 < Chebyshev.theta x) atTop :=
    (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id).eventually_gt_atTop 1
  apply (tendsto_growing_primeProfile_tail_scaled c hc).congr'
  filter_upwards [hTheta, eventually_gt_atTop (0 : Real)] with x ht hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hz : 0 <= c * Real.sqrt x := (mul_pos hc hs).le
  have hFloor : nicolasLogMertensOscillation (Nat.floor x : Real) =
      nicolasLogMertensOscillation x := by
    unfold nicolasLogMertensOscillation nicolasFunction nicolasMertensProduct
    rw [Nat.floor_natCast, <- Chebyshev.theta_eq_theta_coe_floor x]
  have hThetaFloor : 1 < Chebyshev.theta (Nat.floor x : Real) := by
    rw [<- Chebyshev.theta_eq_theta_coe_floor x]
    exact ht
  have hId := nicolasTiltedLog_nat_eq_components (c * Real.sqrt x) hz
    (Nat.floor x) hThetaFloor
  rw [nicolasTiltedLog_natFloor, hFloor] at hId
  rw [hId]
  field_simp
  <;> ring

end PrimeFactorOscillations
