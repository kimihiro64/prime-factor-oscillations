/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralPrincipalAnalytic
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralPrincipalSlotExponents

/-!
# GeneralPrincipalSlotError

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Complete principal slot error on the enlarged strip

The actual compensated replacement and its correction remain coupled.
A general relative-exponent proof gives Q^(-37/50) on the remainder region,
and Q^(-3/4) at the residue. The phase coefficient has norm one.
These are coefficient inputs,not a zero-free bound.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralPrincipalRegion
open scoped Classical
open OAI OAI.SevenEighths
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem principal_raw_correction_half {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta<=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (unramifiedClosed Q A eta 1 s w z-1)<=1/2 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  calc
    _ <= 240*Q^(-(7/5:Real)) :=
      unramifiedClosed_principal_extended_bound Q A eta 1 s w z
        (by linarith) hA heta (by simp) hs hw hz
    _ <= 240*Q^(-1:Real) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ = 240/Q := by rw [Real.rpow_neg_one,<-div_eq_mul_inv]
    _ <= (240:Real)/480 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hQ
    _ = 1/2 := by norm_num

theorem principal_raw_correction_lower {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta<=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    1/2<=norm (unramifiedClosed Q A eta 1 s w z) := by
  have h := principal_raw_correction_half hQ hA heta hs hw hz
  have hn := norm_sub_norm_le (1:Complex) (unramifiedClosed Q A eta 1 s w z)
  rw [norm_one,norm_sub_rev] at hn
  linarith

theorem principal_raw_correction_ne_zero {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta<=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    Not (unramifiedClosed Q A eta 1 s w z=0) :=
  norm_pos_iff.mp ((by norm_num : (0:Real)<1/2).trans_le
    (principal_raw_correction_lower hQ hA heta hs hw hz))

theorem principal_raw_correction_inverse {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta<=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (Inv.inv (unramifiedClosed Q A eta 1 s w z))<=2 := by
  have hh := principal_raw_correction_lower hQ hA heta hs hw hz
  rw [norm_inv,inv_eq_one_div]
  calc
    1/norm (unramifiedClosed Q A eta 1 s w z)<=(1:Real)/(1/2) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hh
    _ = 2 := by norm_num

theorem principal_slot_geometric_bounds {Q : Real} {eta s w z : Complex}
    (hQ : 480<=Q) (heta : norm eta<=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (coordV Q z)<=1/2 /\ norm (coordW Q 1 w)<=1/2 /\
      norm (coordD Q eta 1 s)<=1/2 := by
  have hQ0 : 0<Q := by linarith
  have hQ4 : 4<=Q := by linarith
  refine And.intro ?_ (And.intro ?_ ?_)
  . rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ4 (by linarith)
  . exact (coordW_norm_le Q hQ0 1 w (by simp)).trans
      (rpow_le_half Q _ hQ4 (by linarith))
  . exact (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      (rpow_le_half Q _ hQ4 (by linarith))

theorem principal_region_marked_error_rho {Q : Real} {A eta s w z : Complex} (rho : Real)
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re)
    (hRpow : 4-6*s.re-6*z.re<=-rho)
    (hKVpow : 1-s.re-w.re-6*z.re<=-rho)
    (hBRpow : 4-5*s.re-6*z.re<=-rho)
    (hBKVpow : 1-w.re-6*z.re<=-rho) :
    norm (regionMarked Q A eta s w z+coordD Q eta 1 s)<=28*Q^(-rho) /\
    norm (star eta*(Q:Complex)^s)*
      norm (regionMarked Q A eta s w z+coordD Q eta 1 s)<=28*Q^(-rho) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  have hQ4 : 4 <= Q := by linarith
  have hpow (x y : Real) (h : x <= y) : Q ^ x <= Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 eta s w heta.le
  have hB := principal_B_norm hQ0 eta s heta
  have hg := principal_slot_geometric_bounds hQ heta.le hs hw hz
  have hRhalf : norm (coordR Q A s z) <= 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : norm (coordW Q 1 w) <= 1 := by linarith [hg.2.1]
  have hq : norm ((Inv.inv (Q:Complex))) <= 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    rw [inv_eq_one_div]
    calc
      1/Q<=(1:Real)/1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hQ1
      _ = 1 := by norm_num
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Inv.inv (Q:Complex)) (coordK Q eta s w) (coordW Q 1 w) (coordD Q eta 1 s)
    hRhalf hg.1 hq hg.2.2
  change norm (regionMarked Q A eta s w z + coordD Q eta 1 s) <= _ at hE
  have hRT : norm (coordR Q A s z) <= Q ^ (-rho:Real) := hR.trans (hpow _ _ hRpow)
  have hKV : norm (coordK Q eta s w) * norm (coordV Q z) <= Q ^ (-rho:Real) := by
    calc
      _ <= Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [<- Real.rpow_add hQ0]; congr 1; ring
      _ <= _ := hpow _ _ hKVpow
  have hBR : norm (star eta * (Q : Complex) ^ s) * norm (coordR Q A s z) <= Q ^ (-rho:Real) := by
    calc
      _ <= Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [<- Real.rpow_add hQ0]; congr 1; ring
      _ <= _ := hpow _ _ hBRpow
  have hBKV : norm (star eta * (Q : Complex) ^ s) * (norm (coordK Q eta s w) * norm (coordV Q z)) <=
      Q ^ (-rho:Real) := by
    calc
      _ <= Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [<- Real.rpow_add hQ0, <- Real.rpow_add hQ0]; congr 1; ring
      _ <= _ := hpow _ _ hBKVpow
  have hE' : norm (regionMarked Q A eta s w z + coordD Q eta 1 s) <=
      24 * norm (coordR Q A s z) + 4 * (norm (coordK Q eta s w) * norm (coordV Q z)) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  . linarith
  . have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star eta * (Q : Complex) ^ s))
    nlinarith


theorem principal_region_replacement_error_rho {Q : Real} {A eta s w z : Complex} (rho : Real)
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re)
    (hRpow : 4-6*s.re-6*z.re<=-rho)
    (hKVpow : 1-s.re-w.re-6*z.re<=-rho)
    (hBRpow : 4-5*s.re-6*z.re<=-rho)
    (hBKVpow : 1-w.re-6*z.re<=-rho)
    (hVTpow : -6*z.re<=-rho) (hDTpow : -s.re<=-rho) :
    norm (regionReplacement Q A eta s w z+unramifiedClosed Q A eta 1 s w z)<=
      720*Q^(-rho) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  have hg := principal_slot_geometric_bounds hQ heta.le hs hw hz
  have hWq : coordW Q 1 w=(Q:Complex)^(-w) := by simp [coordW]
  have hq : norm ((Q:Complex)^(-w))<=1 := by rw [<-hWq];linarith [hg.2.1]
  have hW : norm (coordW Q 1 w)<=1 := by linarith [hg.2.1]
  have hVT : norm (coordV Q z)<=Q^(-rho) := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hVTpow
  have hDT : norm (coordD Q eta 1 s)<=Q^(-rho) :=
    (coordD_norm_le Q hQ0 eta 1 s heta.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hDTpow)
  have hE := principal_region_marked_error_rho rho hQ hA heta hs hw hz
    hRpow hKVpow hBRpow hBKVpow
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 eta s heta) hWq

theorem principal_region_slot_error_rho {Q : Real} {A eta s w z : Complex} (rho : Real)
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re)
    (hRpow : 4-6*s.re-6*z.re<=-rho)
    (hKVpow : 1-s.re-w.re-6*z.re<=-rho)
    (hBRpow : 4-5*s.re-6*z.re<=-rho)
    (hBKVpow : 1-w.re-6*z.re<=-rho)
    (hVTpow : -6*z.re<=-rho) (hDTpow : -s.re<=-rho) :
    norm (regionSlot Q A eta s w z+1)<=1440*Q^(-rho) := by
  have hn := principal_raw_correction_ne_zero hQ hA heta.le hs hw hz
  have he := principal_region_replacement_error_rho rho hQ hA heta hs hw hz
    hRpow hKVpow hBRpow hBKVpow hVTpow hDTpow
  have hi := principal_raw_correction_inverse hQ hA heta.le hs hw hz
  have hid : regionSlot Q A eta s w z+1=
      (regionReplacement Q A eta s w z+unramifiedClosed Q A eta 1 s w z)*
        Inv.inv (unramifiedClosed Q A eta 1 s w z) := by
    unfold regionSlot
    field_simp [hn]
  rw [hid,norm_mul]
  calc
    _ <= (720*Q^(-rho))*2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem principal_region_slot_error_extended {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re)
    (hw : (19/20:Real)<=w.re) (hz : (33/200:Real)<=z.re) :
    norm (regionSlot Q A eta s w z+1)<=1440*Q^(-(37/50:Real)) := by
  have hc := principal_relative_exponent_caps s.re w.re z.re hs hw hz
  exact principal_region_slot_error_rho (37/50) hQ hA heta hs (by linarith) (by linarith)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2

theorem principal_slot_residue_error_extended {Q : Real} {A eta s : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re) :
    norm (principalSlot Q A eta s+1)<=1440*Q^(-(3/4:Real)) := by
  have hc := principal_residue_relative_exponent_caps s.re hs
  have hwr : (1:Complex).re=(1:Real) := by simp
  have hzr : (1/6:Complex).re=(1/6:Real) := by norm_num
  have hh := principal_region_slot_error_rho (s:=s) (w:=(1:Complex)) (z:=(1/6:Complex))
    (3/4) hQ hA heta hs (by norm_num) (by norm_num)
    (by simpa only [hwr,hzr] using hc.1)
    (by simpa only [hwr,hzr] using hc.2.1)
    (by simpa only [hwr,hzr] using hc.2.2.1)
    (by simpa only [hwr,hzr] using hc.2.2.2.1)
    (by simpa only [hwr,hzr] using hc.2.2.2.2.1)
    (by simpa only [hwr,hzr] using hc.2.2.2.2.2)
  simpa only [region_slot_at_residue] using hh

theorem principal_region_slot_norm_extended {Q : Real} {A eta s w z : Complex}
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1) (hs : (3/4:Real)<=s.re)
    (hw : (19/20:Real)<=w.re) (hz : (33/200:Real)<=z.re) :
    norm (regionSlot Q A eta s w z)<=1+1440*Q^(-(37/50:Real)) := by
  have he := principal_region_slot_error_extended hQ hA heta hs hw hz
  have hn := norm_sub_le (regionSlot Q A eta s w z+1) (1:Complex)
  rw [add_sub_cancel_right,norm_one] at hn
  linarith

end PrimeFactorOscillations.GeneralPrincipalRegion

