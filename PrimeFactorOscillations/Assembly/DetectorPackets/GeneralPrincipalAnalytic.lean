/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralPrincipalRegion

/-!
# GeneralPrincipalAnalytic

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
# Holomorphy of the principal correction in the enlarged strip

The exact denominators remain nonzero on Re(x)>=3/4,Re(z)>=4/25.
The complete Euler correction is analytic on the corresponding open slices,
is multipliable,and stays away from zero after the proved finite exclusions.
These are inputs to the principal contour transfer,not zero exclusion.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralPrincipalRegion
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic ProbeEuler CompletedGauss ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principal_region_denominators (Q : Real) (A eta v x z : Complex)
    (hQ : 4<=Q) (hA : norm A<=1) (he : norm eta<=1) (hv : norm v<=1)
    (hx : (3/4:Real)<=x.re) (hz : (4/25:Real)<=z.re) :
    Not (1-coordR Q A x z=0) /\ Not (1-coordV Q z=0) /\
      Not (1-coordD Q eta v x=0) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  have hc := principal_coordinate_exponent_caps x.re (9/10:Real) z.re hx le_rfl hz
  have hR : norm (coordR Q A x z)<=1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans
      ((Real.rpow_le_rpow_of_exponent_le hQ1 hc.2.1).trans
        (rpow_le_half Q _ hQ (by norm_num)))
  have hV : norm (coordV Q z)<=1/2 := by
    rw [coordV_norm Q hQ0]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 hc.1).trans
      (rpow_le_half Q _ hQ (by norm_num))
  have hD : norm (coordD Q eta v x)<=1/2 :=
    (coordD_norm_le Q hQ0 eta v x he hv).trans
      ((Real.rpow_le_rpow_of_exponent_le hQ1 hc.2.2.2.1).trans
        (rpow_le_half Q _ hQ (by norm_num)))
  exact And.intro (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR)
    (And.intro (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV)
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD))

theorem unramifiedClosed_principal_analytic_x (Q : Real) (A eta v w z : Complex)
    (hQ : 4<=Q) (hA : norm A<=1) (he : norm eta<=1) (hv : norm v<=1)
    (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun x=>unramifiedClosed Q A eta v x w z)
      {x : Complex | (3/4:Real)<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := principal_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_principal_analytic_w (Q : Real) (A eta v x z : Complex)
    (hQ : 4<=Q) (hA : norm A<=1) (he : norm eta<=1) (hv : norm v<=1)
    (hx : (3/4:Real)<=x.re) (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun w=>unramifiedClosed Q A eta v x w z)
      {w : Complex | (9/10:Real)<w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := principal_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_principal_analytic_z (Q : Real) (A eta v x w : Complex)
    (hQ : 4<=Q) (hA : norm A<=1) (he : norm eta<=1) (hv : norm v<=1)
    (hx : (3/4:Real)<=x.re) :
    AnalyticOnNhd Complex (fun z=>unramifiedClosed Q A eta v x w z)
      {z : Complex | (4/25:Real)<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := principal_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem globalClosedCorrection_principal_multipliable (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    Multipliable (fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>
      idealClosedCorrection eta P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>
    idealClosedCorrection eta P.val x w z
  let B := fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>
    principalPrimeDefectBound P.val
  have hB (P) : norm (F P-1)<=B P :=
    idealClosedCorrection_principal_extended_bound eta P.val
      (hS.norm_four P.val P.property) x w z hx hw hz
  refine Exists.intro (Complex.exp (tsum fun P=>Complex.log (F P))) ?_
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_principal_analytic_x (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (w z : Complex)
    (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun x=>globalClosedCorrection eta S x w z)
      {x : Complex | (3/4:Real)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  . intro P
    apply unramifiedClosed_principal_analytic_x
    . exact_mod_cast hS.norm_four P.val P.property
    . exact actualAPhase_norm_le_one eta _
    . exact HeckeFamily.idealCoeff_norm_le_one eta _
    . simp
    . exact hz
  . intro P x hx
    exact idealClosedCorrection_principal_extended_bound eta P.val
      (hS.norm_four P.val P.property) x w z hx.le hw hz
  . exact hS.half

theorem globalClosedCorrection_principal_analytic_w (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x z : Complex)
    (hx : (3/4:Real)<=x.re) (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun w=>globalClosedCorrection eta S x w z)
      {w : Complex | (9/10:Real)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  . intro P
    apply unramifiedClosed_principal_analytic_w
    . exact_mod_cast hS.norm_four P.val P.property
    . exact actualAPhase_norm_le_one eta _
    . exact HeckeFamily.idealCoeff_norm_le_one eta _
    . simp
    . exact hx
    . exact hz
  . intro P w hw
    exact idealClosedCorrection_principal_extended_bound eta P.val
      (hS.norm_four P.val P.property) x w z hx hw.le hz
  . exact hS.half

theorem globalClosedCorrection_principal_analytic_z (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x w : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) :
    AnalyticOnNhd Complex (fun z=>globalClosedCorrection eta S x w z)
      {z : Complex | (4/25:Real)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  . intro P
    apply unramifiedClosed_principal_analytic_z
    . exact_mod_cast hS.norm_four P.val P.property
    . exact actualAPhase_norm_le_one eta _
    . exact HeckeFamily.idealCoeff_norm_le_one eta _
    . simp
    . exact hx
  . intro P z hz
    exact idealClosedCorrection_principal_extended_bound eta P.val
      (hS.norm_four P.val P.property) x w z hx hw hz.le
  . exact hS.half

theorem idealClosedCorrection_principal_lower_bound (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (P : PrimeIdeal)
    (hP : Not (Membership.mem S P.val)) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    1/2<=norm (idealClosedCorrection eta P x w z) := by
  have hb := (idealClosedCorrection_principal_extended_bound eta P
    (hS.norm_four P hP) x w z hx hw hz).trans (hS.half (Subtype.mk P hP))
  have hn := norm_sub_norm_le (1:Complex) (idealClosedCorrection eta P x w z)
  rw [norm_one,norm_sub_rev] at hn
  linarith

theorem idealClosedCorrection_principal_ne_zero (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (P : PrimeIdeal)
    (hP : Not (Membership.mem S P.val)) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    Not (idealClosedCorrection eta P x w z=0) :=
  norm_pos_iff.mp ((by norm_num : (0:Real)<1/2).trans_le
    (idealClosedCorrection_principal_lower_bound eta S hS P hP x w z hx hw hz))

theorem idealClosedCorrection_principal_inverse_bound (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (P : PrimeIdeal)
    (hP : Not (Membership.mem S P.val)) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (Inv.inv (idealClosedCorrection eta P x w z))<=2 := by
  have hh := idealClosedCorrection_principal_lower_bound eta S hS P hP x w z hx hw hz
  rw [norm_inv,inv_eq_one_div]
  calc
    1/norm (idealClosedCorrection eta P x w z)<=(1:Real)/(1/2) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hh
    _ = 2 := by norm_num

theorem globalClosedCorrection_principal_lower_bound (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    1/2<=norm (globalClosedCorrection eta S x w z) := by
  have hb := globalClosedCorrection_principal_extended_bound eta S hS x w z hx hw hz
  have hn := norm_sub_norm_le (1:Complex) (globalClosedCorrection eta S x w z)
  rw [norm_one,norm_sub_rev] at hn
  linarith

theorem globalClosedCorrection_principal_ne_zero (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    Not (globalClosedCorrection eta S x w z=0) :=
  norm_pos_iff.mp ((by norm_num : (0:Real)<1/2).trans_le
    (globalClosedCorrection_principal_lower_bound eta S hS x w z hx hw hz))

end PrimeFactorOscillations.GeneralPrincipalRegion

