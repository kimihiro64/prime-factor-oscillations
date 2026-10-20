/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified

/-!
# SexticToQuadraticLocal

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
# Exact third-phase extraction from the selected Euler coordinate

Two explicitly retained counterterms replace the leading sextic phase by
its cube. The full V and marked defects remain in the identity. The inverse
Euler denominator is retained. This does not claim a physical realization,
a principal Mellin normalization, or an improved zero-free boundary.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SevenEighths.SexticToQuadraticLocal

open ProbeLocal ProbeEuler

def enhancedReplacement (V W D P B q c : Complex) : Complex :=
  compensatedReplacement V W D P B q+
    continuedCorrection V W D P*c+
    continuedCorrection V W D P*c*D*(1-W)^2

def retainedDefect (V W D P B c : Complex) : Complex :=
  (B+c*(1-W)+c*D*(1-W)^2)*(1-V)*(1-W)*(P+D)+
    c*V*(1-W)^2*(1+D*(1-W)+D^2*(1-W))

theorem exact_third_phase (V W D P B q c : Complex)
    (hD : Not (1-D=0)) (hBD : B*D=c) (hcW : c*W=q) :
    enhancedReplacement V W D P B q c =
      (-c*D^2*(1-W)^3+retainedDefect V W D P B c)/(1-D) := by
  rw [<-hcW]
  unfold enhancedReplacement compensatedReplacement continuedCorrection retainedDefect
  field_simp [hD]
  linear_combination -(1-V)*(1-W)*hBD

theorem selected_inverse_factor (V W D P B q c : Complex)
    (hD : Not (1-D=0)) (hBD : B*D=c) (hcW : c*W=q) :
    (1-D)*enhancedReplacement V W D P B q c =
      -c*D^2*(1-W)^3+retainedDefect V W D P B c := by
  rw [exact_third_phase V W D P B q c hD hBD hcW]
  field_simp [hD]

theorem enhanced_error_bound (V W D P B q c : Complex) (B0 E0 : Real)
    (hV : norm V <= 1/2) (hW : norm W <= 1/2) (hDnorm : norm D <= 1/2)
    (hc : norm c=1) (hB0 : 1 <= B0) (hB : norm B <= B0)
    (hE0 : 0 <= E0) (hE : norm (P+D) <= E0)
    (hBD : B*D=c) (hcW : c*W=q) :
    norm (enhancedReplacement V W D P B q c+c*D^2) <=
      18*B0*E0+10*norm V+(norm D)^2*(10*norm W+2*norm D) := by
  have hden := norm_sub_norm_le (1:Complex) D
  rw [norm_one] at hden
  have hdenpos : 0 < norm (1-D) := by linarith
  have hD : Not (1-D=0) := by
    intro hh
    rw [hh, norm_zero] at hdenpos
    exact (lt_irrefl 0) hdenpos
  have hT : norm (1-W) <= 3/2 := by
    have hh := norm_sub_le (1:Complex) W
    rw [norm_one] at hh
    linarith
  have hVone : norm (1-V) <= 3/2 := by
    have hh := norm_sub_le (1:Complex) V
    rw [norm_one] at hh
    linarith
  have hcoef :
      norm (B+c*(1-W)+c*D*(1-W)^2) <= 4*B0 := by
    calc
      _ <= norm B+norm (c*(1-W))+norm (c*D*(1-W)^2) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ = norm B+norm (1-W)+norm D*(norm (1-W))^2 := by
        simp only [norm_mul, norm_pow, hc, one_mul]
      _ <= 4*B0 := by
        have hT2 : (norm (1-W))^2 <= 9/4 := by nlinarith [norm_nonneg (1-W)]
        have hp := mul_le_mul hDnorm hT2 (sq_nonneg _) (by norm_num : (0:Real) <= 1/2)
        nlinarith
  have hfirst :
      norm ((B+c*(1-W)+c*D*(1-W)^2)*(1-V)*(1-W)*(P+D)) <= 9*B0*E0 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc
      _ <= (4*B0)*(3/2)*(3/2)*E0 := by gcongr
      _ = _ := by ring
  have hsmall :
      norm (1+D*(1-W)+D^2*(1-W)) <= 17/8 := by
    calc
      _ <= norm (1:Complex)+norm (D*(1-W))+norm (D^2*(1-W)) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ = 1+norm D*norm (1-W)+(norm D)^2*norm (1-W) := by
        simp only [norm_one, norm_mul, norm_pow]
      _ <= 17/8 := by
        have hD2 : (norm D)^2 <= 1/4 := by nlinarith [norm_nonneg D]
        have hp := mul_le_mul hDnorm hT (norm_nonneg _) (by norm_num : (0:Real) <= 1/2)
        have hp2 := mul_le_mul hD2 hT (norm_nonneg _) (by norm_num : (0:Real) <= 1/4)
        nlinarith
  have hsecond :
      norm (c*V*(1-W)^2*(1+D*(1-W)+D^2*(1-W))) <= 5*norm V := by
    rw [norm_mul, norm_mul, norm_mul, hc, one_mul, norm_pow]
    have hT2 : (norm (1-W))^2 <= 9/4 := by nlinarith [norm_nonneg (1-W)]
    have hp := mul_le_mul hT2 hsmall (norm_nonneg _) (by norm_num : (0:Real) <= 9/4)
    nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg V), norm_nonneg V]
  have hret : norm (retainedDefect V W D P B c) <= 9*B0*E0+5*norm V := by
    unfold retainedDefect
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hcube : norm ((1-W)^3-1) <= 5*norm W := by
    have hid : (1-W)^3-1 = -W*((1-W)^2+(1-W)+1) := by ring
    rw [hid, norm_mul, norm_neg]
    have hh : norm ((1-W)^2+(1-W)+1) <= 5 := by
      calc
        _ <= norm ((1-W)^2)+norm (1-W)+norm (1:Complex) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ = (norm (1-W))^2+norm (1-W)+1 := by rw [norm_pow, norm_one]
        _ <= 5 := by nlinarith [norm_nonneg (1-W)]
    nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg W)]
  have hmain : norm ((1-D)-(1-W)^3) <= norm D+5*norm W := by
    have hid : (1-D)-(1-W)^3 = -(D+((1-W)^3-1)) := by ring
    rw [hid, norm_neg]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) hcube)
  have hid :
      enhancedReplacement V W D P B q c+c*D^2 =
      (retainedDefect V W D P B c+c*D^2*((1-D)-(1-W)^3))/(1-D) := by
    rw [exact_third_phase V W D P B q c hD hBD hcW]
    field_simp [hD]
    ring
  let A0 : Real := 9*B0*E0+5*norm V+(norm D)^2*(norm D+5*norm W)
  have hA0 : 0 <= A0 := by dsimp [A0]; positivity
  have hn :
      norm (retainedDefect V W D P B c+c*D^2*((1-D)-(1-W)^3)) <= A0 := by
    calc
      _ <= norm (retainedDefect V W D P B c)+norm (c*D^2*((1-D)-(1-W)^3)) := norm_add_le _ _
      _ = norm (retainedDefect V W D P B c)+(norm D)^2*norm ((1-D)-(1-W)^3) := by
        simp only [norm_mul, norm_pow, hc, one_mul]
      _ <= A0 := by dsimp [A0]; gcongr
  rw [hid, norm_div]
  have hhalf : (1/2:Real) <= norm (1-D) := by linarith
  calc
    _ <= A0/(1/2) := by gcongr
    _ = 18*B0*E0+10*norm V+(norm D)^2*(10*norm W+2*norm D) := by dsimp [A0]; ring

def enhancedSelected (Q : Real) (A eta v x w z : Complex) : Complex :=
  enhancedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:Complex)^x)
    ((Q:Complex)^(-w)) (star v)

theorem actual_third_phase (Q : Real) (A eta v x w z : Complex)
    (hQ : 0 < Q) (heta : norm eta=1) (hv : norm v=1)
    (hD : Not (1-coordD Q eta v x=0)) :
    enhancedSelected Q A eta v x w z =
      (-(star v)*(coordD Q eta v x)^2*(1-coordW Q v w)^3+
        retainedDefect (coordV Q z) (coordW Q v w) (coordD Q eta v x)
          (unramifiedMarked Q A eta v x w z)
          (star eta*(Q:Complex)^x) (star v))/(1-coordD Q eta v x) := by
  have hi := selected_phase_identities Q eta v x w hQ heta hv
  exact exact_third_phase _ _ _ _ _ _ _ hD hi.1 hi.2

theorem cubic_phase_coefficient (Q : Real) (eta v x : Complex) (hQ : 0 < Q) :
    star v*(coordD Q eta v x)^2 =
      eta^2*(star v)^3*(Q:Complex)^(-2*x) := by
  have hQ0 : Not ((Q:Complex)=0) := by exact_mod_cast hQ.ne'
  have hp : ((Q:Complex)^(-x))^2=(Q:Complex)^(-2*x) := by
    rw [pow_two, <-Complex.cpow_add _ _ hQ0]
    congr 1
    ring
  unfold coordD
  simp only [mul_pow]
  rw [hp]
  ring

theorem sixth_root_cube_involution (c : Complex) (hc : c^6=1) :
    (c^3)^2=1 := by
  rw [<-pow_mul]
  norm_num
  exact hc

theorem principal_symbol_value (eta : Complex) (heta : eta^2=1) :
    -eta^2*(1:Complex)^3 = -1 := by
  rw [heta]
  ring

end OAI.SevenEighths.SexticToQuadraticLocal

