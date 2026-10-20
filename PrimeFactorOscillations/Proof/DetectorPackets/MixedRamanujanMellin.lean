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
# MixedRamanujanMellin

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
# The complete squarefree Ramanujan Mellin factor

In the mixed carrier kernel t(p) is the full character phase times
Np^(-s), and b selects the primes dividing the nonzero frequency.
The inverse Euler factor is retained. The finite formulas below are
the algebraic part of the ordinary absolutely convergent quotient
on Re(s) > 1; they do not prove a contour shift or zero exclusion.
-/


noncomputable section

namespace PrimeFactorOscillations.MixedRamanujanMellin

def selectedRatio (q t : Complex) : Complex :=
  (1 + (q - 1) * t) / (1 - t)

theorem denominator_nonzero (t : Complex) (ht : norm t < 1) :
    Not (1 - t = 0) := by
  intro he
  have heq : t = 1 := (sub_eq_zero.mp he).symm
  rw [heq, norm_one] at ht
  exact (lt_irrefl (1 : Real)) ht

theorem local_factorization (q t : Complex) (ht : Not (1 - t = 0)) :
    1 + (q - 1) * t = (1 - t) * selectedRatio q t := by
  unfold selectedRatio
  field_simp [ht]

theorem finite_mellin_factorization {I : Type} (S : Finset I)
    (q t : I -> Complex) (b : I -> Prop) [DecidablePred b]
    (ht : forall p, Membership.mem S p -> Not (1 - t p = 0)) :
    S.prod (fun p => 1 + (if b p then q p - 1 else -1) * t p) =
      S.prod (fun p => 1 - t p) *
        (S.filter b).prod (fun p => selectedRatio (q p) (t p)) := by
  classical
  calc
    _ = S.prod (fun p =>
        (1 - t p) * (if b p then selectedRatio (q p) (t p) else 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hb : b p
      . simpa only [ite_eq_left hb] using local_factorization (q p) (t p) (ht p hp)
      . simp only [ite_eq_right hb, neg_mul, one_mul, mul_one]
        ring
    _ = S.prod (fun p => 1 - t p) *
        S.prod (fun p => if b p then selectedRatio (q p) (t p) else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [<- Finset.prod_filter]

theorem inverse_euler_product_nonzero {I : Type} (S : Finset I)
    (t : I -> Complex)
    (ht : forall p, Membership.mem S p -> norm (t p) < 1) :
    Not (S.prod (fun p => 1 - t p) = 0) := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact denominator_nonzero (t p) (ht p hp)

theorem selectedRatio_add (q t : Complex) (ht : Not (1 - t = 0)) :
    selectedRatio q t = 1 + q * t / (1 - t) := by
  unfold selectedRatio
  field_simp [ht]
  ring

theorem selectedRatio_bound (q : Real) (hq : 0 <= q)
    (t : Complex) (ht : norm t < 1) :
    norm (selectedRatio (q : Complex) t) <=
      1 + q * norm t / (1 - norm t) := by
  have hden : 1 - norm t <= norm (1 - t) := by
    have h := norm_add_le (1 - t) t
    have he : (1 - t) + t = (1 : Complex) := by ring
    rw [he, norm_one] at h
    linarith
  have hp : 0 < 1 - norm t := sub_pos.mpr ht
  have hmul : 0 <= q * norm t := mul_nonneg hq (norm_nonneg t)
  rw [selectedRatio_add (q : Complex) t (denominator_nonzero t ht)]
  have h := norm_add_le (1 : Complex) ((q : Complex) * t / (1 - t))
  simp only [norm_one, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hq] at h
  have hfrac := div_le_div_of_nonneg_left hmul hp hden
  linarith

end PrimeFactorOscillations.MixedRamanujanMellin

