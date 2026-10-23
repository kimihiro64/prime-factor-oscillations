/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.ClockRecordEnergy

/-! # Signed finite product ledger for the record process

These identities retain the prime supply before the continuous integral is
inserted. A positive record jump is charged at the actual new record value.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem clockRecordIncrement_complementarity (e : Nat -> Real) (n : Nat) :
    e n * clockRecordIncrement e n =
      clockRecord e (n + 1) * clockRecordIncrement e n := by
  by_cases h : clockRecord e n <= e n
  case pos =>
    have hnext : clockRecord e (n + 1) = e n := max_eq_right h
    rw [hnext]
  case neg =>
    have hnext : clockRecord e (n + 1) = clockRecord e n :=
      max_eq_left (le_of_lt (lt_of_not_ge h))
    simp only [clockRecordIncrement, hnext, sub_self, mul_zero]

theorem clockRecord_product_ledger (e a : Nat -> Real) (n : Nat) :
    clockRecord e n * a n =
      (Finset.range n).sum (fun i => clockRecord e i * (a (i + 1) - a i)) +
        (Finset.range n).sum (fun i => a (i + 1) * clockRecordIncrement e i) := by
  induction n with
  | zero => simp only [clockRecord, Finset.range_zero, Finset.sum_empty, zero_mul, zero_add]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, clockRecordIncrement]
      nlinarith only [ih]

theorem clockRecord_error_product (e : Nat -> Real) (n : Nat) :
    clockRecord e n * clockPreviousError e n = clockRecordSignedEnergy e n +
      (Finset.range n).sum
        (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) := by
  rw [clockRecordSignedEnergy_eq_sum]
  calc
    _ = (Finset.range n).sum
          (fun i => clockRecord e i * (clockPreviousError e (i + 1) -
            clockPreviousError e i)) +
        (Finset.range n).sum
          (fun i => clockPreviousError e (i + 1) * clockRecordIncrement e i) :=
      clockRecord_product_ledger e (clockPreviousError e) n
    _ = _ := by
      have hright :
          (Finset.range n).sum
            (fun i => clockPreviousError e (i + 1) * clockRecordIncrement e i) =
          (Finset.range n).sum
            (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact clockRecordIncrement_complementarity e i
      rw [hright]
      rfl

theorem clockRecord_right_jump_energy (e : Nat -> Real) (n : Nat) :
    2 * (Finset.range n).sum
        (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) =
      (clockRecord e n) ^ 2 + clockRecordQuadraticVariation e n := by
  have hproduct := clockRecord_error_product e n
  have henergy := clockRecordSignedEnergy_identity e n
  nlinarith only [hproduct, henergy]


/-- Signed work of another error against the same record process, centered
at the old record. The two errors are not assumed independent. -/
noncomputable def clockRecordCenteredCrossEnergy
    (e a : Nat -> Real) (m n : Nat) : Real :=
  (Finset.range n).sum
      (fun i => clockRecord e i * (a i - clockPreviousError a i)) -
    (Finset.range m).sum
      (fun i => clockRecord e i * (a i - clockPreviousError a i)) -
    clockRecord e m * (clockPreviousError a n - clockPreviousError a m)

theorem clockRecordCenteredCrossEnergy_product
    (e a : Nat -> Real) (m n : Nat) :
    clockRecordCenteredCrossEnergy e a m n =
      (clockRecord e n - clockRecord e m) * clockPreviousError a n -
        ((Finset.range n).sum (fun i => a i * clockRecordIncrement e i) -
          (Finset.range m).sum (fun i => a i * clockRecordIncrement e i)) := by
  have hn := clockRecord_product_ledger e (clockPreviousError a) n
  have hm := clockRecord_product_ledger e (clockPreviousError a) m
  change clockRecord e n * clockPreviousError a n =
    (Finset.range n).sum (fun i => clockRecord e i *
      (a i - clockPreviousError a i)) +
    (Finset.range n).sum (fun i => a i * clockRecordIncrement e i) at hn
  change clockRecord e m * clockPreviousError a m =
    (Finset.range m).sum (fun i => clockRecord e i *
      (a i - clockPreviousError a i)) +
    (Finset.range m).sum (fun i => a i * clockRecordIncrement e i) at hm
  unfold clockRecordCenteredCrossEnergy
  nlinarith only [hn, hm]

theorem clockRecordCenteredCrossEnergy_add
    (e a b : Nat -> Real) (m n : Nat) :
    clockRecordCenteredCrossEnergy e (fun i => a i + b i) m n =
      clockRecordCenteredCrossEnergy e a m n +
        clockRecordCenteredCrossEnergy e b m n := by
  have hprev (i : Nat) :
      clockPreviousError (fun j => a j + b j) i =
        clockPreviousError a i + clockPreviousError b i := by
    cases i <;> simp only [clockPreviousError, add_zero]
  unfold clockRecordCenteredCrossEnergy
  simp only [hprev, add_sub_add_comm, mul_add, Finset.sum_add_distrib]

theorem clockRecordCenteredCrossEnergy_self
    (e : Nat -> Real) (m n : Nat) :
    clockRecordCenteredCrossEnergy e e m n = clockRecordCenteredEnergy e m n := by
  simp only [clockRecordCenteredCrossEnergy, clockRecordCenteredEnergy,
    clockRecordSignedEnergy_eq_sum]

/-- Exact compensation retains the self-work; the full perturbation work
is removed jointly, including its endpoint and record-jump cross terms. -/
theorem clockRecordCenteredCrossEnergy_compensated
    (e b : Nat -> Real) (m n : Nat)
    (hrecord : clockPreviousError e n = clockRecord e n) :
    2 * (clockRecordCenteredCrossEnergy e (fun i => e i + b i) m n -
        clockRecordCenteredCrossEnergy e b m n) =
      (clockRecord e n - clockRecord e m) ^ 2 -
        (clockRecordQuadraticVariation e n - clockRecordQuadraticVariation e m) := by
  rw [clockRecordCenteredCrossEnergy_add, add_sub_cancel_right,
    clockRecordCenteredCrossEnergy_self]
  have h := clockRecordCenteredEnergy_at_record e m n hrecord
  linarith only [h]



theorem clockRecordCenteredCrossEnergy_bounds
    (e b : Nat -> Real) (m n : Nat) (hmn : m <= n)
    (hb : forall i : Nat, 0 <= b i - clockPreviousError b i) :
    And (0 <= clockRecordCenteredCrossEnergy e b m n)
      (clockRecordCenteredCrossEnergy e b m n <=
        (clockRecord e n - clockRecord e m) *
          (clockPreviousError b n - clockPreviousError b m)) := by
  have hr : Monotone (clockRecord e) := by
    apply monotone_nat_of_le_succ
    intro i
    exact le_max_left _ _
  have hbmono : Monotone (clockPreviousError b) := by
    apply monotone_nat_of_le_succ
    intro i
    change clockPreviousError b i <= b i
    exact sub_nonneg.mp (hb i)
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      simp only [clockRecordCenteredCrossEnergy, sub_self, mul_zero, le_refl,
        clockRecord, clockPreviousError, and_self]
  | succ n ih =>
      by_cases hm : m <= n
      case pos =>
        have hprev := ih m hm
        have hstep :
            clockRecordCenteredCrossEnergy e b m (n + 1) =
              clockRecordCenteredCrossEnergy e b m n +
                (clockRecord e n - clockRecord e m) *
                  (b n - clockPreviousError b n) := by
          simp only [clockRecordCenteredCrossEnergy, Finset.sum_range_succ,
            clockPreviousError]
          ring
        have hk : 0 <= clockRecord e n - clockRecord e m :=
          sub_nonneg.mpr (hr hm)
        have hpos := mul_nonneg hk (hb n)
        have hlast : 0 <= b n - clockPreviousError b m := by
          have h := hbmono (Nat.le_succ_of_le hm)
          simpa only [clockPreviousError] using sub_nonneg.mpr h
        have hinc := mul_nonneg
          (sub_nonneg.mpr (hr (Nat.le_succ n))) hlast
        rw [hstep]
        change And
          (0 <= clockRecordCenteredCrossEnergy e b m n +
            (clockRecord e n - clockRecord e m) * (b n - clockPreviousError b n))
          (clockRecordCenteredCrossEnergy e b m n +
            (clockRecord e n - clockRecord e m) * (b n - clockPreviousError b n) <=
              (clockRecord e (n + 1) - clockRecord e m) *
                (b n - clockPreviousError b m))
        constructor
        . linarith only [hprev.1, hpos]
        . nlinarith only [hprev.2, hinc]
      case neg =>
        have heq : m = n + 1 := by omega
        subst m
        simp only [clockRecordCenteredCrossEnergy, sub_self, mul_zero, le_refl,
          and_self]



/-- Actual deleted mass increment; it is either zero or the full weight. -/
noncomputable def clockDeletedIncrement (e w : Nat -> Real) (i : Nat) : Real :=
  clockDeletedMass e w (i + 1) - clockDeletedMass e w i

noncomputable def clockRetainedHeadroom (e w : Nat -> Real) (i : Nat) : Real :=
  clockDeletedMass e w i - clockPreviousError e i

/-- Retained-prime source minus elapsed time, with the same deleted-mass weight. -/
noncomputable def clockRetainedSignedWork (e w : Nat -> Real) (n : Nat) : Real :=
  (Finset.range n).sum (fun i => clockDeletedMass e w i *
    ((e i - clockPreviousError e i) - clockDeletedIncrement e w i))

noncomputable def clockFullSignedWork (e w : Nat -> Real) (n : Nat) : Real :=
  (Finset.range n).sum
    (fun i => clockDeletedMass e w i * (e i - clockPreviousError e i))

noncomputable def clockDeletedJumpBudget (e w : Nat -> Real) (n : Nat) : Real :=
  (Finset.range n).sum (fun i => w i * clockDeletedIncrement e w i)

theorem clockDeletedMass_product_ledger (e w a : Nat -> Real) (n : Nat) :
    clockDeletedMass e w n * a n =
      (Finset.range n).sum
        (fun i => clockDeletedMass e w i * (a (i + 1) - a i)) +
      (Finset.range n).sum (fun i => a (i + 1) * clockDeletedIncrement e w i) := by
  induction n with
  | zero =>
      simp only [clockDeletedMass, Finset.range_zero, Finset.sum_empty,
        zero_mul, zero_add]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, clockDeletedIncrement]
      nlinarith only [ih]

theorem clockRetainedSignedWork_identity (e w : Nat -> Real) (n : Nat) :
    clockRetainedSignedWork e w n =
      -clockDeletedMass e w n * clockRetainedHeadroom e w n +
      (Finset.range n).sum (fun i =>
        clockRetainedHeadroom e w (i + 1) * clockDeletedIncrement e w i) := by
  have hp := clockDeletedMass_product_ledger e w (clockRetainedHeadroom e w) n
  have hs : clockRetainedSignedWork e w n =
      -(Finset.range n).sum (fun i => clockDeletedMass e w i *
        (clockRetainedHeadroom e w (i + 1) - clockRetainedHeadroom e w i)) := by
    unfold clockRetainedSignedWork
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change clockDeletedMass e w i *
        ((e i - clockPreviousError e i) -
          (clockDeletedMass e w (i + 1) - clockDeletedMass e w i)) =
      -(clockDeletedMass e w i *
        ((clockDeletedMass e w (i + 1) - e i) -
          (clockDeletedMass e w i - clockPreviousError e i)))
    ring
  rw [hs]
  linarith only [hp]

theorem clockDeletedIncrement_headroom_bounds (e w : Nat -> Real) (i : Nat)
    (hw : 0 <= w i)
    (hpre : e i <= clockDeletedMass e w i + w i) :
    And (0 <= clockRetainedHeadroom e w (i + 1) * clockDeletedIncrement e w i)
      (clockRetainedHeadroom e w (i + 1) * clockDeletedIncrement e w i <=
        w i * clockDeletedIncrement e w i) := by
  classical
  by_cases h : e i <= clockDeletedMass e w i
  case pos =>
    have hd : clockDeletedIncrement e w i = 0 := by
      change deletionStep (e i) (w i) (clockDeletedMass e w i) -
        clockDeletedMass e w i = 0
      simp only [deletionStep, ite_eq_left h, sub_self]
    rw [hd, mul_zero, mul_zero]
    exact And.intro (le_refl 0) (le_refl 0)
  case neg =>
    have hd : clockDeletedIncrement e w i = w i := by
      change deletionStep (e i) (w i) (clockDeletedMass e w i) -
        clockDeletedMass e w i = w i
      simp only [deletionStep, ite_eq_right h]
      ring
    have hg : clockRetainedHeadroom e w (i + 1) =
        clockDeletedMass e w i + w i - e i := by
      change deletionStep (e i) (w i) (clockDeletedMass e w i) - e i = _
      simp only [deletionStep, ite_eq_right h]
    rw [hd, hg]
    constructor
    . exact mul_nonneg (sub_nonneg.mpr hpre) hw
    . apply mul_le_mul_of_nonneg_right _ hw
      linarith only [lt_of_not_ge h]

theorem clockRetainedSignedWork_bounds (e w : Nat -> Real) (n : Nat)
    (hw : forall i, 0 <= w i)
    (hpre : forall i, e i <= clockDeletedMass e w i + w i) :
    And (-clockDeletedMass e w n * clockRetainedHeadroom e w n <=
        clockRetainedSignedWork e w n)
      (clockRetainedSignedWork e w n <=
        -clockDeletedMass e w n * clockRetainedHeadroom e w n +
          clockDeletedJumpBudget e w n) := by
  have hlo : 0 <= (Finset.range n).sum (fun i =>
      clockRetainedHeadroom e w (i + 1) * clockDeletedIncrement e w i) :=
    Finset.sum_nonneg (fun i _ =>
      (clockDeletedIncrement_headroom_bounds e w i (hw i) (hpre i)).1)
  have hhi : (Finset.range n).sum (fun i =>
      clockRetainedHeadroom e w (i + 1) * clockDeletedIncrement e w i) <=
      clockDeletedJumpBudget e w n :=
    Finset.sum_le_sum (fun i _ =>
      (clockDeletedIncrement_headroom_bounds e w i (hw i) (hpre i)).2)
  rw [clockRetainedSignedWork_identity]
  exact And.intro (by linarith only [hlo]) (by linarith only [hhi])

theorem clockFullSignedWork_deleted_diagonal (e w : Nat -> Real) (n : Nat) :
    2 * clockFullSignedWork e w n =
      (clockDeletedMass e w n) ^ 2 +
        2 * clockRetainedSignedWork e w n - clockDeletedJumpBudget e w n := by
  classical
  have hsq (i : Nat) :
      (clockDeletedIncrement e w i) ^ 2 = w i * clockDeletedIncrement e w i := by
    by_cases h : e i <= clockDeletedMass e w i
    case pos =>
      have hd : clockDeletedIncrement e w i = 0 := by
        change deletionStep (e i) (w i) (clockDeletedMass e w i) -
          clockDeletedMass e w i = 0
        simp only [deletionStep, ite_eq_left h, sub_self]
      rw [hd]
      ring
    case neg =>
      have hd : clockDeletedIncrement e w i = w i := by
        change deletionStep (e i) (w i) (clockDeletedMass e w i) -
          clockDeletedMass e w i = w i
        simp only [deletionStep, ite_eq_right h]
        ring
      rw [hd]
      ring
  have hquad (k : Nat) :
      (clockDeletedMass e w k) ^ 2 =
        2 * (Finset.range k).sum (fun i =>
          clockDeletedMass e w i * clockDeletedIncrement e w i) +
        (Finset.range k).sum (fun i => w i * clockDeletedIncrement e w i) := by
    induction k with
    | zero =>
        simp only [clockDeletedMass, Finset.range_zero, Finset.sum_empty]
        ring
    | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hd : clockDeletedMass e w (k + 1) =
            clockDeletedMass e w k + clockDeletedIncrement e w k := by
          unfold clockDeletedIncrement
          ring
        rw [hd]
        nlinarith only [ih, hsq k]
  have hsplit : clockFullSignedWork e w n =
      clockRetainedSignedWork e w n +
        (Finset.range n).sum (fun i =>
          clockDeletedMass e w i * clockDeletedIncrement e w i) := by
    unfold clockFullSignedWork clockRetainedSignedWork
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold clockDeletedJumpBudget
  nlinarith only [hsplit, hquad n]

theorem clockFullSignedWork_feedback_bounds (e w : Nat -> Real) (n : Nat)
    (hw : forall i, 0 <= w i)
    (hpre : forall i, e i <= clockDeletedMass e w i + w i) :
    And
      (-clockDeletedJumpBudget e w n / 2 <=
        clockFullSignedWork e w n - (clockDeletedMass e w n) ^ 2 / 2 +
          clockDeletedMass e w n * clockRetainedHeadroom e w n)
      (clockFullSignedWork e w n - (clockDeletedMass e w n) ^ 2 / 2 +
          clockDeletedMass e w n * clockRetainedHeadroom e w n <=
        clockDeletedJumpBudget e w n / 2) := by
  have h := clockRetainedSignedWork_bounds e w n hw hpre
  have hd := clockFullSignedWork_deleted_diagonal e w n
  constructor <;> linarith only [h.1, h.2, hd]


end PrimeFactorOscillations.PrimeClassDeletion
