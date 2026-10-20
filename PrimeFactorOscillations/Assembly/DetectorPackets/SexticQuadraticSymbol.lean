/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.SexticToQuadraticLocal

/-!
# SexticQuadraticSymbol

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
# Uniform quadratic principal symbol of the enhanced selected coordinate

The complete marked defect and V contribution are included. No Mobius
expansion is made on a moved contour. This is a local kernel theorem:
physical counterterm realization and the full signed quotient mean
are separate obligations.
-/

set_option maxHeartbeats 1000000

noncomputable section
namespace OAI.SevenEighths.SexticQuadraticSymbol

open ProbeLocal ProbeEuler SexticToQuadraticLocal

theorem uniform_symbol (Q kappa : Real) (A eta v x w z : Complex)
    (hQ : 1 <= Q) (hk : 0 < kappa) (hsmall : Q^(-kappa) <= 1/2)
    (hA : norm A <= 1) (heta : norm eta=1) (hv : norm v=1)
    (hx : kappa <= x.re) (hw : kappa <= w.re)
    (hRexp : 4-3*x.re-6*z.re <= -kappa)
    (hKVexp : 1+2*x.re-w.re-6*z.re <= -kappa)
    (hVexp : 2*x.re-6*z.re <= -kappa) :
    norm ((Q:Complex)^(2*x)*enhancedSelected Q A eta v x w z+
      eta^2*(star v)^3) <= 526*Q^(-kappa) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQc : Not ((Q:Complex)=0) := by exact_mod_cast hQ0.ne'
  let a : Real := x.re
  let b : Real := w.re
  let c : Real := z.re
  let V : Complex := coordV Q z
  let R : Complex := coordR Q A x z
  let W : Complex := coordW Q v w
  let D : Complex := coordD Q eta v x
  let B : Complex := star eta*(Q:Complex)^x
  let P : Complex := unramifiedMarked Q A eta v x w z
  let q : Complex := (Q:Complex)^(-w)
  have ha : 0 <= a := by dsimp [a]; linarith
  have hpow (p : Real) (hp : p <= -kappa) : Q^p <= Q^(-kappa) :=
    Real.rpow_le_rpow_of_exponent_le hQ hp
  have hRnorm : norm R <= Q^(4-6*a-6*c) :=
    coordR_norm_le Q hQ0 A x z hA
  have hVnorm : norm V = Q^(-6*c) := coordV_norm Q hQ0 z
  have hWnorm : norm W <= Q^(-b) := coordW_norm_le Q hQ0 v w hv.le
  have hDnorm : norm D <= Q^(-a) := coordD_norm_le Q hQ0 eta v x heta.le hv.le
  have hKnorm : norm (coordK Q eta x w) <= Q^(1-a-b) :=
    coordK_norm_le Q hQ eta x w heta.le
  have hRs : norm R <= Q^(-kappa) := hRnorm.trans (hpow _ (by dsimp [a,c] at *; linarith))
  have hVs : norm V <= Q^(-kappa) := by rw [hVnorm]; exact hpow _ (by dsimp [a,c] at *; linarith)
  have hWs : norm W <= Q^(-kappa) := hWnorm.trans (hpow _ (by dsimp [b]; linarith))
  have hDs : norm D <= Q^(-kappa) := hDnorm.trans (hpow _ (by dsimp [a]; linarith))
  have hqInv : norm (Inv.inv (Q:Complex)) <= 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    have hi := one_div_le_one_div_of_le (show (0:Real)<1 by norm_num) hQ
    simpa only [one_div, inv_one] using hi
  have hraw := unramified_marked_error_bound R V (Inv.inv (Q:Complex))
    (coordK Q eta x w) W D (hRs.trans hsmall) (hVs.trans hsmall) hqInv (hDs.trans hsmall)
  have hE : norm (P+D) <= 24*norm R+4*norm (coordK Q eta x w)*norm V := by
    change norm (P+D) <= _ at hraw
    have hm := mul_nonneg (norm_nonneg R) (show 0 <= 1-norm W by linarith [hWs.trans hsmall])
    nlinarith
  have hB : norm B <= Q^a := by
    change norm (star eta*(Q:Complex)^x) <= Q^x.re
    rw [norm_mul, norm_star, heta, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have hB0 : 1 <= Q^a := Real.one_le_rpow hQ ha
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hlocal := enhanced_error_bound V W D P B q (star v) (Q^a)
    (24*norm R+4*norm (coordK Q eta x w)*norm V)
    (hVs.trans hsmall) (hWs.trans hsmall) (hDs.trans hsmall)
    (by rw [norm_star,hv]) hB0 hB (by positivity) hE hi.1 hi.2
  have hphase : (Q:Complex)^(2*x)*(star v*D^2)=eta^2*(star v)^3 := by
    change (Q:Complex)^(2*x)*(star v*(coordD Q eta v x)^2)=_
    rw [cubic_phase_coefficient Q eta v x hQ0]
    calc
      _ = eta^2*(star v)^3*((Q:Complex)^(2*x)*(Q:Complex)^(-2*x)) := by ring
      _ = _ := by rw [<-Complex.cpow_add _ _ hQc]; simp
  have hnorm : norm ((Q:Complex)^(2*x))=Q^(2*a) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    simp [a, Complex.mul_re]
  have hmul :
      norm ((Q:Complex)^(2*x)*enhancedSelected Q A eta v x w z+eta^2*(star v)^3) =
      Q^(2*a)*norm (enhancedReplacement V W D P B q (star v)+star v*D^2) := by
    rw [<-hphase]
    change norm ((Q:Complex)^(2*x)*enhancedReplacement V W D P B q (star v)+
      (Q:Complex)^(2*x)*(star v*D^2))=_
    rw [<-mul_add, norm_mul, hnorm]
  have h1 : Q^(2*a)*Q^a*norm R <= Q^(-kappa) := by
    calc
      _ <= Q^(2*a)*Q^a*Q^(4-6*a-6*c) := by gcongr
      _ = Q^(4-3*a-6*c) := by
        rw [<-Real.rpow_add hQ0, <-Real.rpow_add hQ0]
        congr 1
        ring
      _ <= _ := hpow _ hRexp
  have h2 : Q^(2*a)*Q^a*norm (coordK Q eta x w)*norm V <= Q^(-kappa) := by
    calc
      _ <= Q^(2*a)*Q^a*Q^(1-a-b)*Q^(-6*c) := by rw [hVnorm]; gcongr
      _ = Q^(1+2*a-b-6*c) := by
        rw [<-Real.rpow_add hQ0, <-Real.rpow_add hQ0, <-Real.rpow_add hQ0]
        congr 1
        ring
      _ <= _ := hpow _ hKVexp
  have h3 : Q^(2*a)*norm V <= Q^(-kappa) := by
    rw [hVnorm, <-Real.rpow_add hQ0]
    apply hpow
    dsimp [a,c]
    linarith
  have h4 : Q^(2*a)*(norm D)^2 <= 1 := by
    calc
      _ <= Q^(2*a)*(Q^(-a))^2 := by gcongr
      _ = 1 := by
        rw [<-Real.rpow_natCast, <-Real.rpow_mul hQ0.le, <-Real.rpow_add hQ0]
        have he : 2*a+(-a)*((2:Nat):Real)=0 := by norm_num <;> ring
        rw [he, Real.rpow_zero]
  rw [hmul]
  calc
    _ <= Q^(2*a)*(18*Q^a*(24*norm R+4*norm (coordK Q eta x w)*norm V)+
        10*norm V+(norm D)^2*(10*norm W+2*norm D)) :=
      mul_le_mul_of_nonneg_left hlocal (Real.rpow_nonneg hQ0.le _)
    _ = 432*(Q^(2*a)*Q^a*norm R)+72*(Q^(2*a)*Q^a*norm (coordK Q eta x w)*norm V)+
        10*(Q^(2*a)*norm V)+(Q^(2*a)*(norm D)^2)*(10*norm W+2*norm D) := by ring
    _ <= 432*Q^(-kappa)+72*Q^(-kappa)+10*Q^(-kappa)+
        1*(10*Q^(-kappa)+2*Q^(-kappa)) := by gcongr
    _ = 526*Q^(-kappa) := by ring

end OAI.SevenEighths.SexticQuadraticSymbol

