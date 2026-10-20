/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalNormalization
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Nonlinear coercivity of compensated reciprocal logarithms

Integrated one-coordinate lower bounds and a subadditive boundary gauge retain
all signed reference costs when a finite transport is assembled.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- The exact derivative of the compensated logarithmic profile. -/
theorem hasDerivAt_bernoulliLogProfile (t x : Real) (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (bernoulliLogProfile t) (t ^ 2 / (x ^ 2 * (x + t))) x := by
  have hd := (hasDerivAt_const x t).div (hasDerivAt_id x) hx.ne'
  have hl := (hd.const_add 1).log (by positivity : Not (1 + t / x = 0))
  convert hl.sub hd using 1
  . rfl
  . dsimp only [Pi.div_apply, id_eq]
    field_simp [hx.ne', (add_pos hx ht).ne']
    <;> ring

/-- Probe-uniform integrated lower cost for a coordinate above the reference. -/
theorem incoming_integrated_normalized_pairLogDefect_lower (t r q : Real)
    (ht : 0 < t) (hr : 0 < r) (hrq : r <= q) :
    r / 2 * (1 - (r / q) ^ 2) <=
      r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q := by
  let c := r ^ 2 * (r + t) / t ^ 2
  let F := fun x : Real => c * bernoulliLogProfile t x + (r ^ 3 / 2) / x ^ 2
  let dF := fun x : Real => r ^ 2 * t * (x - r) / (x ^ 3 * (x + t))
  have hder : forall x : Real, 0 < x -> HasDerivAt F (dF x) x := by
    intro x hx
    have hd := ((hasDerivAt_bernoulliLogProfile t x ht hx).const_mul c).add
      ((hasDerivAt_const x (r ^ 3 / 2)).div ((hasDerivAt_id x).pow 2)
        (pow_ne_zero 2 hx.ne'))
    convert hd using 1
    . dsimp [F]
      rfl
    . dsimp [c, dF]
      field_simp [hx.ne', ht.ne', (add_pos hx ht).ne']
      <;> ring
  have hcont : ContinuousOn F (Set.Icc r q) := by
    intro x hx
    exact (hder x (hr.trans_le hx.1)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Set.Icc r q) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc r q) hcont
      (fun x hx => (hder x (hr.trans_le (interior_subset hx).1)).hasDerivWithinAt)
      (by
        intro x hx
        have hxr := (interior_subset hx).1
        have hxpos := hr.trans_le hxr
        dsimp [dF]
        exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg r) ht.le)
          (sub_nonneg.mpr hxr)) (by positivity))
  have h := hmono (Set.left_mem_Icc.mpr hrq) (Set.right_mem_Icc.mpr hrq) hrq
  have hq : 0 < q := hr.trans_le hrq
  have hid : (r ^ 3 / 2) / r ^ 2 - (r ^ 3 / 2) / q ^ 2 =
      r / 2 * (1 - (r / q) ^ 2) := by
    field_simp [hr.ne', hq.ne']
    <;> ring
  change c * bernoulliLogProfile t r + (r ^ 3 / 2) / r ^ 2 <=
    c * bernoulliLogProfile t q + (r ^ 3 / 2) / q ^ 2 at h
  unfold pairLogDefect
  change _ <= c * _
  rw [<- hid]
  nlinarith only [h]

/-- The outgoing cost controls the complete reciprocal displacement. -/
theorem outgoing_integrated_normalized_pairLogDefect_lower (t p r : Real)
    (ht : 0 < t) (hp : 0 < p) (hpr : p <= r) :
    r * (r / p - 1) <= r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t p r := by
  have hr := hp.trans_le hpr
  have hn : 0 <= r ^ 2 * (r + t) / t ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (pairLogDefect_bounds t p r ht.le hp hr).1 hn
  have hid : r ^ 2 * (r + t) / t ^ 2 *
      (t ^ 2 * (r - p) / (p * r * (r + t))) = r * (r / p - 1) := by
    field_simp [hp.ne', hr.ne', ht.ne', (add_pos hr ht).ne']
    <;> ring
  rwa [hid] at h

/-- The saturating boundary gauge, normalized to unit derivative at zero. -/
def reciprocalBoundaryGauge (r d : Real) : Real :=
  r / 2 * (1 - (r / (r + d)) ^ 2)

/-- The nonlinear gauge lies between zero and the original displacement. -/
theorem reciprocalBoundaryGauge_nonneg_le (r d : Real) (hr : 0 < r) (hd : 0 <= d) :
    0 <= reciprocalBoundaryGauge r d /\ reciprocalBoundaryGauge r d <= d := by
  have hden : 0 < r + d := add_pos_of_pos_of_nonneg hr hd
  have hratio : r / (r + d) <= 1 := (div_le_one hden).mpr (by linarith only [hd])
  have hratiopos : 0 <= r / (r + d) := by positivity
  have hsq : (r / (r + d)) ^ 2 <= 1 := by nlinarith only [hratio, hratiopos]
  constructor
  . exact mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
  . have hid : d - reciprocalBoundaryGauge r d =
        d ^ 2 * (3 * r + 2 * d) / (2 * (r + d) ^ 2) := by
      unfold reciprocalBoundaryGauge
      field_simp [hden.ne']
      <;> ring
    have hpos : 0 <= d ^ 2 * (3 * r + 2 * d) / (2 * (r + d) ^ 2) := by positivity
    linarith only [hid, hpos]

/-- Coupling displacements before applying the gauge only lowers the cost. -/
theorem reciprocalBoundaryGauge_subadd (r x y : Real)
    (hr : 0 < r) (hx : 0 <= x) (hy : 0 <= y) :
    reciprocalBoundaryGauge r (x + y) <=
      reciprocalBoundaryGauge r x + reciprocalBoundaryGauge r y := by
  have hrx : 0 < r + x := add_pos_of_pos_of_nonneg hr hx
  have hry : 0 < r + y := add_pos_of_pos_of_nonneg hr hy
  have hrxy : 0 < r + (x + y) := by positivity
  let a := r / (r + x)
  let b := r / (r + y)
  let c := r / (r + (x + y))
  have ha : 0 <= a := by dsimp [a]; positivity
  have hb : 0 <= b := by dsimp [b]; positivity
  have hc : 0 <= c := by dsimp [c]; positivity
  have ha1 : a <= 1 := (div_le_one hrx).mpr (by linarith only [hx])
  have hb1 : b <= 1 := (div_le_one hry).mpr (by linarith only [hy])
  have hab : a * b <= c := by
    have hid : c - a * b = r * x * y / ((r + x) * (r + y) * (r + (x + y))) := by
      dsimp [a, b, c]
      field_simp [hrx.ne', hry.ne', hrxy.ne']
      <;> ring
    have hpos : 0 <= r * x * y / ((r + x) * (r + y) * (r + (x + y))) := by positivity
    linarith only [hid, hpos]
  have ha2 : a ^ 2 <= 1 := by nlinarith only [ha, ha1]
  have hb2 : b ^ 2 <= 1 := by nlinarith only [hb, hb1]
  have hprod := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have habc : (a * b) ^ 2 <= c ^ 2 := by nlinarith only [hab, hc, mul_nonneg ha hb]
  have hsum : 1 - c ^ 2 <= (1 - a ^ 2) + (1 - b ^ 2) := by
    nlinarith only [hprod, habc]
  have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 <= r / 2)
  simpa only [reciprocalBoundaryGauge, a, b, c, mul_add] using h

/-- The entire finite displacement is controlled before summing reference costs. -/
theorem reciprocalBoundaryGauge_sum_le {I : Type*} (s : Finset I)
    (d : I -> Real) (r : Real) (hr : 0 < r)
    (hd : forall i, Membership.mem s i -> 0 <= d i) :
    reciprocalBoundaryGauge r (Finset.sum s d) <=
      Finset.sum s (fun i => reciprocalBoundaryGauge r (d i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reciprocalBoundaryGauge, hr.ne']
  | @insert a s ha ih =>
      have hda := hd a (Finset.mem_insert_self a s)
      have hds : forall i, Membership.mem s i -> 0 <= d i := by
        intro i hi
        exact hd i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (reciprocalBoundaryGauge_subadd r (d a) (Finset.sum s d) hr hda
        (Finset.sum_nonneg hds)).trans
        (_root_.add_le_add (le_refl _) (ih hds))

/-- Nonlinear coercivity for the complete signed transport across a reference. -/
theorem normalized_reference_transport_nonlinear_lower {I : Type*} [DecidableEq I]
    (s u : Finset I) (p : I -> Real) (t r : Real) (hc : s.card = u.card)
    (ht : 0 < t) (hr : 0 < r)
    (hin : forall i, Membership.mem (s \ u) i -> r <= p i)
    (hout : forall i, Membership.mem (u \ s) i -> 0 < p i /\ p i <= r) :
    reciprocalBoundaryGauge r (Finset.sum s p - Finset.sum u p) <=
      r ^ 2 * (r + t) / t ^ 2 *
        (Finset.sum s (fun i => bernoulliLogProfile t (p i)) -
          Finset.sum u (fun i => bernoulliLogProfile t (p i))) := by
  have hdi : forall i, Membership.mem (s \ u) i -> 0 <= p i - r := by
    intro i hi
    exact sub_nonneg.mpr (hin i hi)
  have hdo : forall i, Membership.mem (u \ s) i -> 0 <= r - p i := by
    intro i hi
    exact sub_nonneg.mpr (hout i hi).2
  rw [Finset.sum_sub_sum_eq_reference_transport s u p r hc,
    Finset.sum_sub_sum_eq_reference_transport s u
      (fun i => bernoulliLogProfile t (p i)) (bernoulliLogProfile t r) hc]
  calc
    _ <= reciprocalBoundaryGauge r (Finset.sum (s \ u) (fun i => p i - r)) +
        reciprocalBoundaryGauge r (Finset.sum (u \ s) (fun i => r - p i)) :=
      reciprocalBoundaryGauge_subadd r _ _ hr
        (Finset.sum_nonneg hdi) (Finset.sum_nonneg hdo)
    _ <= Finset.sum (s \ u) (fun i => reciprocalBoundaryGauge r (p i - r)) +
        Finset.sum (u \ s) (fun i => reciprocalBoundaryGauge r (r - p i)) :=
      _root_.add_le_add
        (reciprocalBoundaryGauge_sum_le _ _ r hr hdi)
        (reciprocalBoundaryGauge_sum_le _ _ r hr hdo)
    _ <= _ := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      apply _root_.add_le_add
      . apply Finset.sum_le_sum
        intro i hi
        rw [reciprocalBoundaryGauge, show r + (p i - r) = p i by ring]
        exact incoming_integrated_normalized_pairLogDefect_lower t r (p i) ht hr (hin i hi)
      . apply Finset.sum_le_sum
        intro i hi
        exact (reciprocalBoundaryGauge_nonneg_le r (r - p i) hr (hdo i hi)).2.trans
          (reference_gap_le_normalized_pairLogDefect t (p i) r ht
            (hout i hi).1 (hout i hi).2)

/-- Every budget below the half-reference threshold bounds the entire displacement. -/
theorem reciprocalBoundaryGauge_inverse_bound (r S C : Real)
    (hr : 0 < r) (hS : 0 <= S) (hC : C < r / 2)
    (hcost : reciprocalBoundaryGauge r S <= C) :
    S <= r * (1 / Real.sqrt (1 - 2 * C / r) - 1) := by
  have hden : 0 < r + S := add_pos_of_pos_of_nonneg hr hS
  have hfrac : 2 * C / r < 1 := (div_lt_one hr).mpr (by linarith only [hC])
  have hA : 0 < 1 - 2 * C / r := sub_pos.mpr hfrac
  have ha : 0 < Real.sqrt (1 - 2 * C / r) := Real.sqrt_pos.mpr hA
  have ha2 := Real.sq_sqrt hA.le
  have hratio : 0 <= r / (r + S) := by positivity
  have hm := mul_le_mul_of_nonneg_right hcost (by positivity : 0 <= 2 / r)
  have hid : reciprocalBoundaryGauge r S * (2 / r) =
      1 - (r / (r + S)) ^ 2 := by
    unfold reciprocalBoundaryGauge
    field_simp [hr.ne']
    <;> ring
  have hb : 1 - (r / (r + S)) ^ 2 <= 2 * C / r := by
    rw [hid] at hm
    calc
      _ <= C * (2 / r) := hm
      _ = 2 * C / r := by ring
  have hroot : Real.sqrt (1 - 2 * C / r) <= r / (r + S) := by
    nlinarith only [ha2, hb, ha, hratio]
  have hmul := mul_le_mul_of_nonneg_right hroot hden.le
  have hcancel : r / (r + S) * (r + S) = r := by field_simp [hden.ne']
  rw [hcancel] at hmul
  have hm2 := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 <= 1 / Real.sqrt (1 - 2 * C / r))
  have hcancel2 : Real.sqrt (1 - 2 * C / r) * (r + S) *
      (1 / Real.sqrt (1 - 2 * C / r)) = S + r := by
    calc
      _ = (Real.sqrt (1 - 2 * C / r) / Real.sqrt (1 - 2 * C / r)) * (r + S) := by ring
      _ = S + r := by rw [div_self ha.ne', one_mul]; ring
  have hsum : S + r <= r / Real.sqrt (1 - 2 * C / r) := by
    rw [hcancel2] at hm2
    simpa only [mul_one_div] using hm2
  calc
    S <= r / Real.sqrt (1 - 2 * C / r) - r := by linarith only [hsum]
    _ = r * (1 / Real.sqrt (1 - 2 * C / r) - 1) := by ring

end Real
