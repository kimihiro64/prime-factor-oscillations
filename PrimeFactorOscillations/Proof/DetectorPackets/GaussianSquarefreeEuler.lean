/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# GaussianSquarefreeEuler

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
# Squarefree quartic Gaussian Euler kernel

The local expressions retain the principal and both nonprincipal sectors.
Their ordinary arithmetic derivation uses the zero-extended quartic symbol,
the prime-power Gauss table and the column calibration mu times conjugate
normalized Gauss. This file proves their rational identities, the exact
principal marked ratio, its uniform error and finite-product nonvanishing.
It does not formalize the Gauss table, infinite Euler product, Mellin
continuation, packet estimate or a new zero-free region.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianSquarefreeEuler

def localFactor (q a v t : Complex) : Complex :=
  1/(1-t)+v/(1-v)-a-(q-1)*a*v*t/(1-t)

def numerator (q a v t : Complex) : Complex :=
  1-v*t-a*(1-t)*(1-v)-(q-1)*a*v*t*(1-v)

def correction (q a v t : Complex) : Complex :=
  numerator q a v t/(1-a)

def markedNumerator (q a v t B c : Complex) : Complex :=
  (B-c)*(1-v)*(-a*(1-t)-(q-1)*a*v*t)-c*(1-v*t)

def markedCorrection (q a v t B c : Complex) : Complex :=
  markedNumerator q a v t B c/(1-a)

theorem local_factorization (q a v t : Complex)
    (ht : Not (1-t=0)) (hv : Not (1-v=0)) :
    localFactor q a v t=numerator q a v t/((1-t)*(1-v)) := by
  unfold localFactor numerator
  field_simp [ht, hv]
  ring

theorem correction_defect (q a v t : Complex) (ha : Not (1-a=0)) :
    correction q a v t-1=
      (a*(t+v-t*v)-v*t-(q-1)*a*v*t*(1-v))/(1-a) := by
  unfold correction numerator
  field_simp [ha]
  ring

theorem marked_keeps_all_sectors (q a v t B c : Complex) :
    markedNumerator q a v t B c=
      B*(1-v)*(-a*(1-t)-(q-1)*a*v*t)-c*numerator q a v t := by
  unfold markedNumerator numerator
  ring

theorem principal_numerator (q a : Complex) (hq : Not (q=0)) :
    numerator q a (1/q) (1/q)=
      (1-1/q^2)*(1-(1-1/q)*a) := by
  unfold numerator
  field_simp [hq]
  ring

theorem principal_marked_numerator (q a B : Complex)
    (hq : Not (q=0)) (hBa : B*a=1) :
    markedNumerator q a (1/q) (1/q) B (1/q)=
      (1-1/q^2)*(-1+(1/q)*(1-1/q)*a) := by
  have ha : Not (a=0) := by
    intro hz
    rw [hz, mul_zero] at hBa
    exact zero_ne_one hBa
  have hB : B=1/a := (eq_div_iff ha).mpr hBa
  rw [hB]
  unfold markedNumerator
  field_simp [hq, ha]
  ring

def principalCore (h : Real) (a : Complex) : Complex :=
  1-(1-(h:Complex))*a

def principalCorrection (h : Real) (a : Complex) : Complex :=
  (1-(h:Complex)^2)*principalCore h a/(1-a)

def principalMarkedRatio (h : Real) (a : Complex) : Complex :=
  (-1+(h:Complex)*(1-(h:Complex))*a)/principalCore h a

theorem principal_correction_identity (q : Real) (a : Complex)
    (hq : Not (q=0)) :
    correction (q:Complex) a (1/(q:Complex)) (1/(q:Complex))=
      principalCorrection (1/q) a := by
  have hqc : Not ((q:Complex)=0) := by exact_mod_cast hq
  unfold correction principalCorrection principalCore
  rw [principal_numerator (q:Complex) a hqc]
  push_cast
  ring

theorem principal_core_nonzero (h : Real) (hh0 : 0 <= h) (hh1 : h <= 1)
    (a : Complex) (ha : norm a < 1) :
    Not (principalCore h a=0) := by
  have hn : norm ((1-(h:Complex))*a) < 1 := by
    rw [norm_mul, <-Complex.ofReal_one, <-Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hb : (1-h)*norm a <= norm a := by
      nlinarith [norm_nonneg a]
    exact hb.trans_lt ha
  intro hz
  have he : (1-(h:Complex))*a=1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl (1:Real)) hn

theorem principal_correction_nonzero (h : Real) (hh0 : 0 < h) (hh1 : h < 1)
    (a : Complex) (ha : norm a < 1) :
    Not (principalCorrection h a=0) := by
  have hc := principal_core_nonzero h hh0.le hh1.le a ha
  have hd : Not (1-a=0) := by
    intro hz
    have he : a=1 := (sub_eq_zero.mp hz).symm
    rw [he, norm_one] at ha
    exact (lt_irrefl (1:Real)) ha
  have hf : Not (1-(h:Complex)^2=0) := by
    have hr : Not (1-h^2=0) := by nlinarith
    exact_mod_cast hr
  unfold principalCorrection
  exact div_ne_zero (mul_ne_zero hf hc) hd

theorem marked_ratio_error (h : Real) (a : Complex)
    (hc : Not (principalCore h a=0)) :
    principalMarkedRatio h a+1=
      -((1-(h:Complex))^2*a)/principalCore h a := by
  unfold principalMarkedRatio principalCore at *
  field_simp [hc]
  ring

theorem marked_ratio_error_bound (h : Real) (hh0 : 0 <= h) (hh1 : h <= 1)
    (a : Complex) (ha : norm a <= 1/2) :
    norm (principalMarkedRatio h a+1) <= 2*norm a := by
  have ha1 : norm a < 1 := by linarith
  have hc := principal_core_nonzero h hh0 hh1 a ha1
  have hn : norm ((1-(h:Complex))*a) <= norm a := by
    rw [norm_mul, <-Complex.ofReal_one, <-Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg a]
  have ht := norm_add_le (principalCore h a) ((1-(h:Complex))*a)
  have he : principalCore h a+(1-(h:Complex))*a=1 := by
    unfold principalCore
    ring
  rw [he, norm_one] at ht
  have hcl : 1/2 <= norm (principalCore h a) := by linarith
  have hcp : 0 < norm (principalCore h a) := by linarith
  have hsq : (1-h)^2 <= 1 := by nlinarith
  rw [marked_ratio_error h a hc, norm_div, norm_neg, norm_mul, norm_pow]
  rw [<-Complex.ofReal_one, <-Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  calc
    (1-h)^2*norm a/norm (principalCore h a) <=
        norm a/norm (principalCore h a) :=
      div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg a) hsq) hcp.le
    _ <= norm a/(1/2) :=
      div_le_div_of_nonneg_left (norm_nonneg a) (by norm_num) hcl
    _ = 2*norm a := by ring

theorem finite_principal_product_nonzero {I : Type*} (S : Finset I)
    (h : I -> Real) (a : I -> Complex)
    (hh : forall i, Membership.mem S i -> 0 < h i /\ h i < 1)
    (ha : forall i, Membership.mem S i -> norm (a i) < 1) :
    Not (S.prod (fun i => principalCorrection (h i) (a i))=0) := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact principal_correction_nonzero (h i) (hh i hi).1 (hh i hi).2 (a i) (ha i hi)

def ramifiedOne (q b t : Complex) : Complex :=
  1+b*(1-q*t)

def ramifiedHigher (q b : Complex) : Complex :=
  1-(q-1)*b

theorem ramified_one_sector_identity (q b t : Complex) (ht : Not (1-t=0)) :
    1/(1-t)+b-(q-1)*b*t/(1-t)=ramifiedOne q b t/(1-t) := by
  unfold ramifiedOne
  field_simp [ht]
  ring

theorem ramified_higher_sector_identity (q b t : Complex) (ht : Not (1-t=0)) :
    1/(1-t)-(q-1)*b/(1-t)=ramifiedHigher q b/(1-t) := by
  unfold ramifiedHigher
  field_simp [ht]

end PrimeFactorOscillations.GaussianSquarefreeEuler
