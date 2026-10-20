/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralPrincipalSlotError
import PrimeFactorOscillations.Assembly.DetectorPackets.PuncturedQuadraticPrincipal

/-!
# PuncturedQuadraticReference

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
# Full reference ratio of the physically punctured quadratic probe

The constant local Euler polynomial is not itself the ratio to the fixed
global reference. Restoring the removed Euler factors and the old correction
gives -(1-Q^(-1))^4 / ((1-D)*C). Its uniform error on Re(s)>=3/4
has an explicit upper bound. No reciprocal L-function norm bound is assumed or proved.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SevenEighths.PuncturedQuadraticReference

open ProbeLocal ProbeEuler SexticToQuadraticLocal
open PuncturedQuadraticPrincipal
open PrimeFactorOscillations.GeneralPrincipalRegion

def referenceSlot (Q : Real) (A eta s : Complex) : Complex :=
  (Q:Complex)^(2*s)*(1-coordV Q (1/6))*
    enhancedReplacement 0 (coordW Q 1 1) (coordD Q eta 1 s)
      (-coordD Q eta 1 s) (star eta*(Q:Complex)^s)
      ((Q:Complex)^(-(1:Complex))) 1/
    unramifiedClosed Q A eta 1 s 1 (1/6)

theorem reference_identity (Q : Real) (A eta s : Complex)
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1)
    (heta2 : eta^2=1) (hs : (3/4:Real)<=s.re) :
    referenceSlot Q A eta s =
      -(1-(Q:Complex)^(-(1:Complex)))^4/
        ((1-coordD Q eta 1 s)*unramifiedClosed Q A eta 1 s 1 (1/6)) := by
  have hQ0 : 0<Q := by linarith
  have hg := principal_slot_geometric_bounds hQ heta.le hs
    (show (9/10:Real)<=(1:Complex).re by norm_num)
    (show (4/25:Real)<=((1/6:Complex).re) by norm_num)
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hW := one_sub_ne_zero_of_norm_le_half _ hg.2.1
  have hC := principal_raw_correction_ne_zero hQ hA heta.le hs
    (show (9/10:Real)<=(1:Complex).re by norm_num)
    (show (4/25:Real)<=((1/6:Complex).re) by norm_num)
  have hv : coordV Q (1/6)=(Q:Complex)^(-(1:Complex)) := by
    unfold coordV
    congr 1
    ring
  have he := principal_exact Q eta s hQ0 heta heta2 hW hD
  unfold referenceSlot
  rw [hv]
  unfold coordW
  simp only [one_mul]
  unfold coordW at he
  simp only [one_mul] at he
  unfold coordW at hW
  simp only [one_mul] at hW
  field_simp [hD, hC, hW] at he
  field_simp [hD, hC]
  linear_combination he

theorem fourth_power_error (q : Complex) (hq : norm q<=1) :
    norm ((1-q)^4-1)<=15*norm q := by
  have h2 : (norm q)^2<=1 := by nlinarith [norm_nonneg q]
  have h3 : (norm q)^3<=1 := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg q)]
  have hp : norm (4-6*q+4*q^2-q^3)<=15 := by
    calc
      _ <= norm (4-6*q+4*q^2)+norm (q^3) := norm_sub_le _ _
      _ <= norm (4-6*q)+norm (4*q^2)+norm (q^3) := by
        linarith [norm_add_le (4-6*q) (4*q^2)]
      _ <= norm (4:Complex)+norm (6*q)+norm (4*q^2)+norm (q^3) := by
        linarith [norm_sub_le (4:Complex) (6*q)]
      _ = 4+6*norm q+4*(norm q)^2+(norm q)^3 := by
        simp only [norm_mul, norm_pow]
        norm_num
      _ <= 15 := by linarith
  rw [show (1-q)^4-1= -q*(4-6*q+4*q^2-q^3) by ring, norm_mul, norm_neg]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg q)

theorem coupled_ratio_error (q D C : Complex) (T : Real)
    (hq : norm q<=1) (hqT : norm q<=T) (hDT : norm D<=T)
    (hD : norm D<=1/2) (hC : norm (C-1)<=1/2)
    (hCT : norm (C-1)<=240*T) :
    norm (-(1-q)^4/((1-D)*C)+1)<=1026*T := by
  have hT : 0<=T := (norm_nonneg q).trans hqT
  have hCnorm : norm C<=3/2 := by
    have hb := norm_add_le (C-1) (1:Complex)
    rw [sub_add_cancel, norm_one] at hb
    linarith
  have hClower : 1/2<=norm C := by
    have hb := norm_sub_norm_le (1:Complex) C
    rw [norm_one, norm_sub_rev] at hb
    linarith
  have hC0 : Not (C=0) := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hClower)
  have hD0 := one_sub_ne_zero_of_norm_le_half D hD
  have hN0 : Not ((1-D)*C=0) := mul_ne_zero hD0 hC0
  have hCi : norm (Inv.inv C)<=2 := by
    rw [norm_inv, inv_eq_one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hClower).trans_eq (by norm_num)
  have hNi : norm (Inv.inv ((1-D)*C))<=4 := by
    rw [mul_inv_rev, norm_mul]
    exact (mul_le_mul hCi (inv_one_sub_norm_le_two D hD)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hN1 : norm ((1-D)*C-1)<=240*T+(3/2)*T := by
    rw [show (1-D)*C-1=(C-1)-D*C by ring]
    calc
      _ <= norm (C-1)+norm (D*C) := norm_sub_le _ _
      _ = norm (C-1)+norm D*norm C := by rw [norm_mul]
      _ <= 240*T+T*(3/2) := by gcongr
      _ = _ := by ring
  have hnum : norm ((1-D)*C-(1-q)^4)<=240*T+(3/2)*T+15*T := by
    calc
      _ = norm (((1-D)*C-1)-((1-q)^4-1)) := by congr 1; ring
      _ <= norm ((1-D)*C-1)+norm ((1-q)^4-1) := norm_sub_le _ _
      _ <= 240*T+(3/2)*T+15*norm q := add_le_add hN1 (fourth_power_error q hq)
      _ <= _ := by gcongr
  rw [show -(1-q)^4/((1-D)*C)+1=
    (((1-D)*C-(1-q)^4)*Inv.inv ((1-D)*C)) by field_simp [hN0]; ring, norm_mul]
  calc
    _ <= (240*T+(3/2)*T+15*T)*4 :=
      mul_le_mul hnum hNi (norm_nonneg _) (by positivity)
    _ = 1026*T := by ring

theorem reference_error (Q : Real) (A eta s : Complex)
    (hQ : 480<=Q) (hA : norm A<=1) (heta : norm eta=1)
    (heta2 : eta^2=1) (hs : (3/4:Real)<=s.re) :
    norm (referenceSlot Q A eta s+1)<=1026*Q^(-(3/4:Real)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  have hg := principal_slot_geometric_bounds hQ heta.le hs
    (show (9/10:Real)<=(1:Complex).re by norm_num)
    (show (4/25:Real)<=((1/6:Complex).re) by norm_num)
  have hhalf := principal_raw_correction_half hQ hA heta.le hs
    (show (9/10:Real)<=(1:Complex).re by norm_num)
    (show (4/25:Real)<=((1/6:Complex).re) by norm_num)
  have hCT : norm (unramifiedClosed Q A eta 1 s 1 (1/6)-1)<=
      240*Q^(-(3/4:Real)) := by
    apply (unramifiedClosed_principal_extended_bound Q A eta 1 s 1 (1/6)
      (by linarith) hA heta.le (by simp) hs (by norm_num) (by norm_num)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
  have hqnorm : norm ((Q:Complex)^(-(1:Complex)))=Q^(-1:Real) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    norm_num
  have hq : norm ((Q:Complex)^(-(1:Complex)))<=1 := by
    rw [hqnorm]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (show (-1:Real)<=0 by norm_num)).trans_eq
      (Real.rpow_zero Q)
  have hqT : norm ((Q:Complex)^(-(1:Complex)))<=Q^(-(3/4:Real)) := by
    rw [hqnorm]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hDT : norm (coordD Q eta 1 s)<=Q^(-(3/4:Real)) := by
    apply (coordD_norm_le Q hQ0 eta 1 s heta.le (by simp)).trans
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  rw [reference_identity Q A eta s hQ hA heta heta2 hs]
  exact coupled_ratio_error _ _ _ _ hq hqT hDT hg.2.2 hhalf hCT

end OAI.SevenEighths.PuncturedQuadraticReference

