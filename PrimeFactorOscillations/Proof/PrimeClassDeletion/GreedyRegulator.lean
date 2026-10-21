/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite greedy clocks and their retained record signal

The clock increment assumption includes the elapsed positive time.
The exact rejection rule and its signed slack ledger are retained.
The asymptotic wave transfer in the paper is an ordinary proof.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def deletionStep (e w m : Real) : Real := by
  classical
  exact if e <= m then m else m + w

theorem deletionStep_record_bounds (e w m r : Real)
    (hrm : r <= m) (hmr : m <= r + w) (hpre : e <= m + w) :
    max r e <= deletionStep e w m /\
      deletionStep e w m <= max r e + w := by
  classical
  unfold deletionStep
  by_cases h : e <= m
  case pos =>
    rw [ite_eq_left h]
    have hmax := le_max_left r e
    exact And.intro (max_le hrm h) (by linarith only [hmr, hmax])
  case neg =>
    rw [ite_eq_right h]
    have hme : m < e := lt_of_not_ge h
    rw [max_eq_right (hrm.trans hme.le)]
    exact And.intro hpre (by linarith only [hme])

/-- The positive mass and the record increment remain coupled. -/
theorem deletionStep_signed_slack (e w m r : Real) :
    deletionStep e w m - max r e =
      (m - r) + (if e <= m then 0 else w) - (max r e - r) := by
  classical
  unfold deletionStep
  by_cases h : e <= m
  case pos =>
    rw [ite_eq_left h, ite_eq_left h]
    linarith
  case neg =>
    rw [ite_eq_right h, ite_eq_right h]
    linarith

noncomputable def clockDeletedMass (e w : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => deletionStep (e n) (w n) (clockDeletedMass e w n)

noncomputable def clockRecord (e : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => max (clockRecord e n) (e n)

theorem clockRecord_nonneg (e : Nat -> Real) (n : Nat) :
    0 <= clockRecord e n := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem clockRecord_contains (e : Nat -> Real) (n : Nat) :
    e n <= clockRecord e (n + 1) := by
  exact le_max_right _ _

/-- Increasing weights and the actual clock increment imply the complete
record sandwich at every finite prefix. -/
theorem clockDeletedMass_record_bounds (e w : Nat -> Real)
    (hw0 : 0 <= w 0) (hw : Monotone w)
    (hinit : e 0 <= w 0)
    (hclock : forall n, e (n + 1) <= e n + w (n + 1))
    (n : Nat) :
    clockRecord e n <= clockDeletedMass e w n /\
      clockDeletedMass e w n <= clockRecord e n + w n := by
  induction n with
  | zero =>
      exact And.intro (le_refl 0) (by simpa only [clockDeletedMass, clockRecord, zero_add] using hw0)
  | succ n ih =>
      have hpre : e n <= clockDeletedMass e w n + w n := by
        cases n with
        | zero => simpa only [clockDeletedMass, zero_add] using hinit
        | succ k =>
            have hinput := hclock k
            have hprefix := (clockRecord_contains e k).trans ih.1
            linarith only [hinput, hprefix]
      have hstep := deletionStep_record_bounds (e n) (w n)
        (clockDeletedMass e w n) (clockRecord e n) ih.1 ih.2 hpre
      refine And.intro hstep.1 ?_
      have hweight := hw (Nat.le_succ n)
      change deletionStep (e n) (w n) (clockDeletedMass e w n) <=
        max (clockRecord e n) (e n) + w (n + 1)
      linarith only [hstep.2, hweight]

theorem clockDeletedMass_record_error (e w : Nat -> Real)
    (hw0 : 0 <= w 0) (hw : Monotone w)
    (hinit : e 0 <= w 0)
    (hclock : forall n, e (n + 1) <= e n + w (n + 1))
    (n : Nat) :
    0 <= clockDeletedMass e w n - clockRecord e n /\
      clockDeletedMass e w n - clockRecord e n <= w n := by
  have h := clockDeletedMass_record_bounds e w hw0 hw hinit hclock n
  exact And.intro (by linarith only [h.1]) (by linarith only [h.2])

theorem clockDeletedMass_rejection_is_record (e w : Nat -> Real)
    (hw0 : 0 <= w 0) (hw : Monotone w)
    (hinit : e 0 <= w 0)
    (hclock : forall n, e (n + 1) <= e n + w (n + 1))
    (n : Nat) (hreject : clockDeletedMass e w n < e n) :
    clockRecord e n < e n /\
      clockDeletedMass e w (n + 1) = clockDeletedMass e w n + w n := by
  classical
  have h := clockDeletedMass_record_bounds e w hw0 hw hinit hclock n
  refine And.intro (h.1.trans_lt hreject) ?_
  change deletionStep (e n) (w n) (clockDeletedMass e w n) = _
  unfold deletionStep
  rw [ite_eq_right (not_le.mpr hreject)]

end PrimeFactorOscillations.PrimeClassDeletion
