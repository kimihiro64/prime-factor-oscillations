/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalEndpoint

/-!
# The exact endpoint envelope of a finite positive probe sum

Every finite sum lies below the larger rational endpoint. Explicit positive
small or large probes exceed every strictly smaller budget, so the envelope
is sharp without assuming or exchanging an asymptotic limit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

def finiteLogDeficit {I : Type*} (s : Finset I) (p : I -> Real) (t r : Real) : Real :=
  s.sum (fun i => normalizedLogDeficit t r (p i))

def logDeficitQuadraticEndpoint {I : Type*} (s : Finset I) (p : I -> Real) (r : Real) : Real :=
  s.sum (fun i => r ^ 3 / (2 * (p i) ^ 2))

def logDeficitReciprocalEndpoint {I : Type*} (s : Finset I) (p : I -> Real) (r : Real) : Real :=
  s.sum (fun i => r ^ 2 / p i)

def logDeficitCubicControl {I : Type*} (s : Finset I) (p : I -> Real) (r : Real) : Real :=
  s.sum (fun i => r ^ 3 / (2 * (p i) ^ 3))

/-- The same positive convex coefficients work for every coordinate in the finite sum. -/
theorem finiteLogDeficit_le_max_endpoints {I : Type*} (s : Finset I) (p : I -> Real)
    (t r : Real) (ht : 0 < t) (hr : 0 < r)
    (hp : forall i, Membership.mem s i -> 0 < p i) :
    finiteLogDeficit s p t r <=
      max (logDeficitQuadraticEndpoint s p r) (logDeficitReciprocalEndpoint s p r) := by
  let A := logDeficitQuadraticEndpoint s p r
  let B := logDeficitReciprocalEndpoint s p r
  have hsum := Finset.sum_le_sum (s := s)
    (fun i hi => normalizedLogDeficit_le_endpoint_convex t r (p i) ht hr (hp i hi))
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum] at hsum
  change finiteLogDeficit s p t r <= r / (r + t) * A + t / (r + t) * B at hsum
  have hleft := mul_le_mul_of_nonneg_left (le_max_left A B)
    (by positivity : 0 <= r / (r + t))
  have hright := mul_le_mul_of_nonneg_left (le_max_right A B)
    (by positivity : 0 <= t / (r + t))
  have hweights : r / (r + t) + t / (r + t) = 1 := by
    field_simp [(add_pos hr ht).ne']
  have hconv : r / (r + t) * max A B + t / (r + t) * max A B = max A B := by
    rw [<- add_mul, hweights, one_mul]
  change finiteLogDeficit s p t r <= max A B
  linarith only [hsum, hleft, hright, hconv]

/-- A finite cubic control gives a uniform linear error near the quadratic endpoint. -/
theorem finiteLogDeficit_small_probe_lower {I : Type*} (s : Finset I) (p : I -> Real)
    (t r : Real) (ht : 0 < t) (hr : 0 < r)
    (hp : forall i, Membership.mem s i -> 0 < p i) :
    logDeficitQuadraticEndpoint s p r - t * logDeficitCubicControl s p r <=
      finiteLogDeficit s p t r := by
  have h := Finset.sum_le_sum (s := s)
    (fun i hi => normalizedLogDeficit_small_probe_lower t r (p i) ht hr (hp i hi))
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum] at h
  exact h

/-- The tangent parameter gives an explicit finite-sum error near the reciprocal endpoint. -/
theorem finiteLogDeficit_large_probe_lower {I : Type*} (s : Finset I) (p : I -> Real)
    (t r a : Real) (ht : 0 < t) (hr : 0 < r)
    (hp : forall i, Membership.mem s i -> 0 < p i) (ha : 1 <= a) :
    (1 - 1 / a) * logDeficitReciprocalEndpoint s p r - (s.card : Real) * r ^ 2 * a / t <=
      finiteLogDeficit s p t r := by
  have h := Finset.sum_le_sum (s := s)
    (fun i hi => normalizedLogDeficit_large_probe_lower t r (p i) a ht hr (hp i hi) ha)
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, Finset.sum_const] at h
  simp only [nsmul_eq_mul] at h
  have hid : (s.card : Real) * (r ^ 2 * a / t) = (s.card : Real) * r ^ 2 * a / t := by ring
  rw [hid] at h
  exact h

/-- A concrete positive probe exceeds any budget below the quadratic endpoint. -/
theorem finiteLogDeficit_exists_small_probe {I : Type*} (s : Finset I) (p : I -> Real)
    (r C : Real) (hr : 0 < r) (hs : s.Nonempty)
    (hp : forall i, Membership.mem s i -> 0 < p i)
    (hC : C < logDeficitQuadraticEndpoint s p r) :
    exists t : Real, 0 < t /\ C < finiteLogDeficit s p t r := by
  let A := logDeficitQuadraticEndpoint s p r
  let H := logDeficitCubicControl s p r
  have hH : 0 < H := by
    dsimp only [H, logDeficitCubicControl]
    exact Finset.sum_pos (fun i hi => by have hpi := hp i hi; positivity) hs
  have hdelta : 0 < A - C := sub_pos.mpr hC
  let t := (A - C) / (2 * H)
  have ht : 0 < t := by dsimp only [t]; positivity
  have h := finiteLogDeficit_small_probe_lower s p t r ht hr hp
  change A - t * H <= finiteLogDeficit s p t r at h
  have hid : t * H = (A - C) / 2 := by
    dsimp only [t]
    field_simp [hH.ne']
  rw [hid] at h
  refine Exists.intro t (And.intro ht ?_)
  change C < A at hC
  linarith only [h, hC]

/-- A concrete large positive probe exceeds any budget below the reciprocal endpoint. -/
theorem finiteLogDeficit_exists_large_probe {I : Type*} (s : Finset I) (p : I -> Real)
    (r C : Real) (hr : 0 < r) (hs : s.Nonempty)
    (hp : forall i, Membership.mem s i -> 0 < p i)
    (hC : C < logDeficitReciprocalEndpoint s p r) :
    exists t : Real, 0 < t /\ C < finiteLogDeficit s p t r := by
  let B := logDeficitReciprocalEndpoint s p r
  let delta := B - C
  have hB : 0 < B := by
    dsimp only [B, logDeficitReciprocalEndpoint]
    exact Finset.sum_pos (fun i hi => by have hpi := hp i hi; positivity) hs
  have hdelta : 0 < delta := sub_pos.mpr hC
  have hcard : (0 : Real) < s.card := by exact_mod_cast (Finset.card_pos.mpr hs)
  let a := 1 + 4 * B / delta
  have ha : 1 <= a := by
    have hnonneg : 0 <= 4 * B / delta := by positivity
    dsimp only [a]
    linarith only [hnonneg]
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let t := 4 * (s.card : Real) * r ^ 2 * a / delta
  have ht : 0 < t := by dsimp only [t]; positivity
  have hidA : a * delta = delta + 4 * B := by
    dsimp only [a]
    field_simp [hdelta.ne']
  have hquot : B / a < delta / 4 := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) ha0.le
    have hidB : B / a * a = B := by field_simp [ha0.ne']
    rw [hidB] at hm
    nlinarith only [hm, hidA, hdelta]
  have hidError : (s.card : Real) * r ^ 2 * a / t = delta / 4 := by
    dsimp only [t]
    field_simp [hcard.ne', hr.ne', ha0.ne', hdelta.ne']
  have hprod : (1 - 1 / a) * B = B - B / a := by ring
  have h := finiteLogDeficit_large_probe_lower s p t r a ht hr hp ha
  change (1 - 1 / a) * B - (s.card : Real) * r ^ 2 * a / t <=
    finiteLogDeficit s p t r at h
  rw [hprod, hidError] at h
  refine Exists.intro t (And.intro ht ?_)
  change C < B at hC
  dsimp only [delta] at h hquot
  linarith only [h, hquot, hC]

/-- The complete positive-probe supremum is exactly the larger rational endpoint. -/
theorem finiteLogDeficit_exists_probe_iff {I : Type*} (s : Finset I) (p : I -> Real)
    (r C : Real) (hr : 0 < r) (hs : s.Nonempty)
    (hp : forall i, Membership.mem s i -> 0 < p i) :
    (exists t : Real, 0 < t /\ C < finiteLogDeficit s p t r) <->
      C < max (logDeficitQuadraticEndpoint s p r) (logDeficitReciprocalEndpoint s p r) := by
  constructor
  . intro h
    let t := Classical.choose h
    have ht := Classical.choose_spec h
    exact ht.2.trans_le (finiteLogDeficit_le_max_endpoints s p t r ht.1 hr hp)
  . intro h
    cases lt_max_iff.mp h with
    | inl hA => exact finiteLogDeficit_exists_small_probe s p r C hr hs hp hA
    | inr hB => exact finiteLogDeficit_exists_large_probe s p r C hr hs hp hB

/-- The rational endpoint envelope is the actual least upper bound of the positive-probe values. -/
theorem finiteLogDeficit_isLUB {I : Type*} (s : Finset I) (p : I -> Real)
    (r : Real) (hr : 0 < r) (hs : s.Nonempty)
    (hp : forall i, Membership.mem s i -> 0 < p i) :
    IsLUB {x : Real | exists t : Real, 0 < t /\ x = finiteLogDeficit s p t r}
      (max (logDeficitQuadraticEndpoint s p r) (logDeficitReciprocalEndpoint s p r)) := by
  constructor
  . intro x hx
    let t := Classical.choose hx
    have ht := Classical.choose_spec hx
    calc
      x = finiteLogDeficit s p t r := ht.2
      _ <= _ := finiteLogDeficit_le_max_endpoints s p t r ht.1 hr hp
  . intro y hy
    by_contra hn
    have hgap : y < max (logDeficitQuadraticEndpoint s p r)
        (logDeficitReciprocalEndpoint s p r) := lt_of_not_ge hn
    have hex := (finiteLogDeficit_exists_probe_iff s p r y hr hs hp).mpr hgap
    let t := Classical.choose hex
    have ht := Classical.choose_spec hex
    have hle := hy (Exists.intro t (And.intro ht.1 rfl))
    exact (not_lt_of_ge hle) ht.2

end Real
