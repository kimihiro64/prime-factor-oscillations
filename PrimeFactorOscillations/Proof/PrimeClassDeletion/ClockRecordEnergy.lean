/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyRegulator

/-! # Exact signed energy of the existing positive-record clock

The energy retains the full terminal slack. The quadratic variation is
the sum of the actual record increments squared. No cancellation estimate
or zero-free improvement is assumed or asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

def clockPreviousError (e : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => e n

noncomputable def clockRecordIncrement (e : Nat -> Real) (n : Nat) : Real :=
  clockRecord e (n + 1) - clockRecord e n

noncomputable def clockRecordSignedEnergy (e : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => clockRecordSignedEnergy e n +
      clockRecord e n * (e n - clockPreviousError e n)

noncomputable def clockRecordQuadraticVariation (e : Nat -> Real) (n : Nat) : Real :=
  (Finset.range n).sum (fun i => (clockRecordIncrement e i) ^ 2)

theorem clockRecordIncrement_nonneg (e : Nat -> Real) (n : Nat) :
    0 <= clockRecordIncrement e n := by
  change 0 <= max (clockRecord e n) (e n) - clockRecord e n
  exact sub_nonneg.mpr (le_max_left _ _)

theorem clockRecordIncrement_sum (e : Nat -> Real) (n : Nat) :
    (Finset.range n).sum (clockRecordIncrement e) = clockRecord e n := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, clockRecord]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, clockRecordIncrement]
      ring

theorem clockRecordSignedEnergy_eq_sum (e : Nat -> Real) (n : Nat) :
    clockRecordSignedEnergy e n =
      (Finset.range n).sum (fun i => clockRecord e i * (e i - clockPreviousError e i)) := by
  induction n with
  | zero => simp only [clockRecordSignedEnergy, Finset.range_zero, Finset.sum_empty]
  | succ n ih => rw [clockRecordSignedEnergy, Finset.sum_range_succ, ih]

theorem clockRecordQuadraticVariation_succ (e : Nat -> Real) (n : Nat) :
    clockRecordQuadraticVariation e (n + 1) =
      clockRecordQuadraticVariation e n +
        (clockRecord e (n + 1) - clockRecord e n) ^ 2 := by
  simp only [clockRecordQuadraticVariation, Finset.sum_range_succ, clockRecordIncrement]

theorem clockRecordSignedEnergy_identity (e : Nat -> Real) (n : Nat) :
    (clockRecord e n) ^ 2 = 2 * clockRecordSignedEnergy e n +
      2 * clockRecord e n * (clockRecord e n - clockPreviousError e n) +
        clockRecordQuadraticVariation e n := by
  induction n with
  | zero =>
      simp only [clockRecord, clockRecordSignedEnergy, clockPreviousError,
        clockRecordQuadraticVariation, Finset.range_zero, Finset.sum_empty,
        zero_pow (by decide : Not (2 = 0)), mul_zero, add_zero, sub_self]
  | succ n ih =>
      rw [clockRecordQuadraticVariation_succ]
      simp only [clockRecordSignedEnergy]
      rw [show clockPreviousError e (n + 1) = e n from rfl]
      by_cases h : clockRecord e n <= e n
      case pos =>
        have hnext : clockRecord e (n + 1) = e n := max_eq_right h
        rw [hnext]
        nlinarith only [ih]
      case neg =>
        have hnext : clockRecord e (n + 1) = clockRecord e n :=
          max_eq_left (le_of_lt (lt_of_not_ge h))
        rw [hnext]
        nlinarith only [ih]

theorem clockRecordQuadraticVariation_nonneg (e : Nat -> Real) (n : Nat) :
    0 <= clockRecordQuadraticVariation e n :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (clockRecordIncrement e i))

theorem clockRecordQuadraticVariation_le (e : Nat -> Real) (n : Nat) (W : Real)
    (hW : forall i : Nat, i < n -> clockRecordIncrement e i <= W) :
    clockRecordQuadraticVariation e n <= W * clockRecord e n := by
  calc
    clockRecordQuadraticVariation e n <=
        (Finset.range n).sum (fun i => W * clockRecordIncrement e i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hW i (Finset.mem_range.mp hi))
        (clockRecordIncrement_nonneg e i)
    _ = W * clockRecord e n := by
      rw [<- Finset.mul_sum, clockRecordIncrement_sum]

theorem clockRecordIncrement_le_of_clock (e w : Nat -> Real)
    (hw : forall i : Nat, 0 <= w i) (hinit : e 0 <= w 0)
    (hclock : forall i : Nat, e (i + 1) <= e i + w (i + 1)) (n : Nat) :
    clockRecordIncrement e n <= w n := by
  have hpre : e n <= clockRecord e n + w n := by
    cases n with
    | zero => simpa only [clockRecord, zero_add] using hinit
    | succ k =>
        have he := clockRecord_contains e k
        have hc := hclock k
        linarith only [he, hc]
  change max (clockRecord e n) (e n) - clockRecord e n <= w n
  have hmax : max (clockRecord e n) (e n) <= clockRecord e n + w n :=
    max_le (le_add_of_nonneg_right (hw n)) hpre
  linarith only [hmax]

theorem clockRecordSignedEnergy_at_record (e : Nat -> Real) (n : Nat)
    (hrecord : clockPreviousError e n = clockRecord e n) :
    (clockRecord e n) ^ 2 =
      2 * clockRecordSignedEnergy e n + clockRecordQuadraticVariation e n := by
  simpa only [hrecord, sub_self, mul_zero, add_zero] using
    clockRecordSignedEnergy_identity e n

/-! The centered interval energy removes the old record's contribution to
the change of the error. It retains every signed clock increment. -/

noncomputable def clockRecordCenteredEnergy (e : Nat -> Real) (m n : Nat) : Real :=
  clockRecordSignedEnergy e n - clockRecordSignedEnergy e m -
    clockRecord e m * (clockPreviousError e n - clockPreviousError e m)

theorem clockRecordCenteredEnergy_identity (e : Nat -> Real) (m n : Nat) :
    (clockRecord e n - clockRecord e m) ^ 2 =
      2 * clockRecordCenteredEnergy e m n +
        2 * (clockRecord e n - clockRecord e m) *
          (clockRecord e n - clockPreviousError e n) +
        (clockRecordQuadraticVariation e n - clockRecordQuadraticVariation e m) := by
  have hn := clockRecordSignedEnergy_identity e n
  have hm := clockRecordSignedEnergy_identity e m
  dsimp only [clockRecordCenteredEnergy]
  nlinarith only [hn, hm]

theorem clockRecordCenteredEnergy_at_record (e : Nat -> Real) (m n : Nat)
    (hrecord : clockPreviousError e n = clockRecord e n) :
    (clockRecord e n - clockRecord e m) ^ 2 =
      2 * clockRecordCenteredEnergy e m n +
        (clockRecordQuadraticVariation e n - clockRecordQuadraticVariation e m) := by
  simpa only [hrecord, sub_self, mul_zero, add_zero] using
    clockRecordCenteredEnergy_identity e m n

theorem clockRecordQuadraticVariation_interval_le
    (e : Nat -> Real) (m n : Nat) (W : Real) (hmn : m <= n)
    (hInc : forall i : Nat, m <= i -> i < n -> clockRecordIncrement e i <= W) :
    clockRecordQuadraticVariation e n - clockRecordQuadraticVariation e m <=
      W * (clockRecord e n - clockRecord e m) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      simp only [sub_self, mul_zero, le_refl]
  | succ n ih =>
      by_cases hm : m <= n
      case pos =>
        have hprev := ih m hm (fun i hmi hin => hInc i hmi (Nat.lt_succ_of_lt hin))
        have hsq : (clockRecordIncrement e n) ^ 2 <= W * clockRecordIncrement e n := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right (hInc n hm (Nat.lt_succ_self n))
            (clockRecordIncrement_nonneg e n)
        dsimp only [clockRecordIncrement] at hsq
        rw [clockRecordQuadraticVariation_succ]
        nlinarith only [hprev, hsq]
      case neg =>
        have heq : m = n + 1 := by omega
        subst m
        simp only [sub_self, mul_zero, le_refl]

/-! This is a conditional barrier certificate, not a bound on its signed
energy hypothesis. In particular, it assumes no independent prime gaps. -/

theorem clockRecordCenteredEnergy_barrier
    (e : Nat -> Real) (m n : Nat) (W A : Real)
    (hmn : m <= n) (hW : 0 <= W) (hA : 0 <= A)
    (hInc : forall i : Nat, m <= i -> i < n -> clockRecordIncrement e i <= W)
    (hrecord : clockPreviousError e n = clockRecord e n)
    (hEnergy : 2 * clockRecordCenteredEnergy e m n <= A ^ 2) :
    clockRecord e n <= clockRecord e m + W + A := by
  have hid := clockRecordCenteredEnergy_at_record e m n hrecord
  have hq := clockRecordQuadraticVariation_interval_le e m n W hmn hInc
  have hbound : (clockRecord e n - clockRecord e m) ^ 2 <=
      A ^ 2 + W * (clockRecord e n - clockRecord e m) := by
    linarith only [hid, hq, hEnergy]
  by_contra hbad
  have hk : W + A < clockRecord e n - clockRecord e m := by
    linarith only [lt_of_not_ge hbad]
  have hleft : 0 < clockRecord e n - clockRecord e m - W - A := by
    linarith only [hk]
  have hright : 0 < clockRecord e n - clockRecord e m + A := by
    linarith only [hk, hW, hA]
  have hprod := mul_pos hleft hright
  have hWA := mul_nonneg hW hA
  nlinarith only [hbound, hprod, hWA]

/-! Sublinearity forces arbitrarily late balanced record endpoints. The
overshoot term is essential: an arbitrary jump is not a smooth crossing. -/

theorem sublinearClock_balanced_records
    (r w : Nat -> Real) (hr : Monotone r)
    (hUnbounded : forall B : Real, Exists fun n : Nat => B < r n)
    (hJump : forall n : Nat, 0 < n -> r n - r (n - 1) <= w n)
    (hSublinear : forall c : Real, 0 < c -> Exists fun M : Nat =>
      forall n : Nat, M <= n -> r n <= c * (n : Real))
    (N : Nat) :
    Exists fun p : Nat => And (N <= p)
      (And (r (p - 1) < r p) (r p - w p <= 2 * r (p / 2))) := by
  classical
  by_contra hNo
  have hBad (p : Nat) (hpN : N <= p) (hrec : r (p - 1) < r p) :
      2 * r (p / 2) < r p - w p := by
    apply lt_of_not_ge
    intro hGood
    exact hNo (Exists.intro p (And.intro hpN (And.intro hrec hGood)))
  have hStep (n : Nat) (hn : N <= n) : 2 * r n < r (2 * n) := by
    have hExists : Exists fun p : Nat => r (2 * n) < r p :=
      hUnbounded (r (2 * n))
    let p := Nat.find hExists
    have hp : r (2 * n) < r p := Nat.find_spec hExists
    have hnp : 2 * n < p := by
      by_contra h
      have hmono := hr (le_of_not_gt h)
      linarith only [hp, hmono]
    have hp0 : 0 < p := by omega
    have hprev : r (p - 1) = r (2 * n) := by
      have hle : r (p - 1) <= r (2 * n) := by
        by_contra h
        have hmin := Nat.find_min' hExists (lt_of_not_ge h)
        change p <= p - 1 at hmin
        omega
      exact le_antisymm hle (hr (by omega))
    have hrec : r (p - 1) < r p := by rw [hprev]; exact hp
    have hbad := hBad p (by omega) hrec
    have hjump := hJump p hp0
    have hhalf := hr (show n <= p / 2 by omega)
    linarith only [hbad, hjump, hhalf, hprev]
  choose q hq using hUnbounded 0
  let n0 : Nat := max (max N 1) q
  have hnN : N <= n0 := (le_max_left N 1).trans (le_max_left (max N 1) q)
  have hnOne : 1 <= n0 := (le_max_right N 1).trans (le_max_left (max N 1) q)
  have hrPos : 0 < r n0 := hq.trans_le (hr (le_max_right (max N 1) q))
  have hnPos : (0 : Real) < (n0 : Real) := by exact_mod_cast (by omega : 0 < n0)
  let c : Real := r n0 / (2 * (n0 : Real))
  have hc : 0 < c := div_pos hrPos (mul_pos (by norm_num) hnPos)
  choose M hM using hSublinear c hc
  have hPowLower : forall k : Nat, k + 1 <= (2 : Nat) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have hGrowth : forall k : Nat,
      (((2 : Nat) ^ k : Nat) : Real) * r n0 <= r ((2 : Nat) ^ k * n0) := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Nat.cast_one, one_mul, le_refl]
    | succ k ih =>
        have hOne : 1 <= (2 : Nat) ^ k := by have h := hPowLower k; omega
        have hn : n0 <= (2 : Nat) ^ k * n0 := by
          simpa only [one_mul] using Nat.mul_le_mul_right n0 hOne
        have hs := hStep ((2 : Nat) ^ k * n0) (hnN.trans hn)
        have hNat : (2 : Nat) ^ (k + 1) * n0 = 2 * ((2 : Nat) ^ k * n0) := by
          rw [pow_succ]
          ring
        have hCast : (((2 : Nat) ^ (k + 1) : Nat) : Real) =
            2 * (((2 : Nat) ^ k : Nat) : Real) := by
          rw [pow_succ, Nat.cast_mul]
          norm_num
          ring
        rw [hNat, hCast]
        linarith only [ih, hs]
  have hLarge : M <= (2 : Nat) ^ M * n0 := by
    have hpow := hPowLower M
    have hmul := Nat.mul_le_mul_left ((2 : Nat) ^ M) hnOne
    omega
  have hUpper := hM ((2 : Nat) ^ M * n0) hLarge
  have hcEq : c * (n0 : Real) = r n0 / 2 := by
    dsimp only [c]
    field_simp [hnPos.ne']
  have hUpper' : r ((2 : Nat) ^ M * n0) <=
      (((2 : Nat) ^ M : Nat) : Real) * (r n0 / 2) := by
    calc
      _ <= c * (((2 : Nat) ^ M * n0 : Nat) : Real) := hUpper
      _ = _ := by rw [Nat.cast_mul, <- hcEq]; ring
  have hLower := hGrowth M
  have hPowPos : (0 : Real) < (((2 : Nat) ^ M : Nat) : Real) := by
    exact_mod_cast (by have h := hPowLower M; omega : 0 < (2 : Nat) ^ M)
  have hprod := mul_pos hPowPos hrPos
  nlinarith only [hUpper', hLower, hprod]

end PrimeFactorOscillations.PrimeClassDeletion
