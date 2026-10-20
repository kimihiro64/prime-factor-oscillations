/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Ring

/-!
# QuarticCompensatedLocal

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
# Row-independent quartic compensation coordinates

The conjugate normalized Gauss branches remove the moving character.
This checks the phase algebra, fourth-power Mellin scale and finite
local convolution. Gaussian Gauss sums and packet means are not built here.
-/


noncomputable section
namespace PrimeFactorOscillations.QuarticCompensatedLocal

def incoming (e a g : Complex) : Complex := e*a*g

def outgoing (e a g : Complex) : Complex := -e*a^3*star g

theorem unit_pair (g : Complex) (hg : norm g = 1) :
    g*star g = 1 := by
  have hh := Complex.mul_conj g
  change g*star g = (Complex.normSq g : Complex) at hh
  simpa only [Complex.normSq_eq_norm_sq, hg, one_pow, Complex.ofReal_one] using hh

theorem phase_product (e a g : Complex) (he : e^2 = 1) (hg : norm g = 1) :
    incoming e a g*outgoing e a g = -a^4 := by
  unfold incoming outgoing
  calc
    (e*a*g)*(-e*a^3*star g) = -(e^2)*a^4*(g*star g) := by ring
    _ = -a^4 := by rw [he, unit_pair g hg]; ring

theorem counterterm_numerator (e a g t : Complex)
    (he : e^2 = 1) (hg : norm g = 1) :
    incoming e a g*outgoing e a g*t = -(a^4*t) := by
  rw [phase_product e a g he hg]
  ring

theorem regularized_local (q M B : Complex) :
    (1-q)*M+q*B = M+q*(B-M) := by
  ring

theorem local_recovery (q M B F Z : Complex)
    (hlevel : (1-q)*M = F*Z-q*B) :
    M+q*(B-M) = F*Z := by
  rw [<-regularized_local q M B, hlevel]
  ring

theorem mellin_scale (P s : Complex) (hP : Not (P = 0)) :
    P^((1/2:Complex)-s)*P^((5/2:Complex)-3*s) =
      P^(-1:Complex)*P^(-4*(s-1)) := by
  rw [<-Complex.cpow_add _ _ hP, <-Complex.cpow_add _ _ hP]
  congr 1
  ring

theorem central_coordinate_norm (a : Complex) (P : Real)
    (ha : norm a = 1) (hP : 0 < P) :
    norm (a^4/(P:Complex)) = 1/P := by
  rw [norm_div, norm_pow, ha, one_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hP]

theorem central_denominator_nonzero (a : Complex) (P : Real)
    (ha : norm a = 1) (hP : 1 < P) :
    Not (1-a^4/(P:Complex) = 0) := by
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hn : norm (a^4/(P:Complex)) < 1 := by
    rw [central_coordinate_norm a P ha hP0]
    exact (div_lt_one hP0).mpr hP
  intro hh
  have hq : a^4/(P:Complex) = 1 := (sub_eq_zero.mp hh).symm
  rw [hq, norm_one] at hn
  exact (lt_irrefl (1:Real)) hn

theorem finite_counterterm (q : Complex) (N : Nat) :
    (1-q)*(Finset.range N).sum (fun j => q^(j+1)) = q-q^(N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [pow_succ]
    ring

end PrimeFactorOscillations.QuarticCompensatedLocal

