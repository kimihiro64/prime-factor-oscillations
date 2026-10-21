/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Sparse repair mass retained by regularized Hellinger energy

A common nonnegative floor preserves the signed difference of capacities
and weights. Its square-root energy controls positive repair mass up to
the capacity on the actual repair support. These finite inequalities are
the algebraic consumer for the ordinary Poisson/RH criterion in the paper.
Infinite product measures and the analytic RH criterion are not proved here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def repairHellingerEnergy (a w delta : Real) : Real :=
  (Real.sqrt (w + delta) - Real.sqrt (a + delta)) ^ 2

theorem repairHellingerEnergy_nonneg (a w delta : Real) :
    0 <= repairHellingerEnergy a w delta := by
  exact sq_nonneg _

theorem regularized_capacity_pos (a delta : Real)
    (ha : 0 <= a) (hd : 0 < delta) : 0 < a + delta := by
  linarith

theorem repairHellingerEnergy_le_abs (a w delta : Real)
    (ha : 0 <= a) (hw : 0 <= w) (hd : 0 <= delta) :
    repairHellingerEnergy a w delta <= abs (w - a) := by
  have hsa := Real.sq_sqrt (add_nonneg ha hd)
  have hsw := Real.sq_sqrt (add_nonneg hw hd)
  have hna := Real.sqrt_nonneg (a + delta)
  have hnw := Real.sqrt_nonneg (w + delta)
  unfold repairHellingerEnergy
  by_cases haw : a <= w
  case pos =>
    rw [abs_of_nonneg (sub_nonneg.mpr haw)]
    have hroot : Real.sqrt (a + delta) <= Real.sqrt (w + delta) :=
      Real.sqrt_le_sqrt (by linarith)
    have hprod := mul_nonneg hna (sub_nonneg.mpr hroot)
    nlinarith
  case neg =>
    have hwa : w <= a := (lt_of_not_ge haw).le
    rw [abs_of_nonpos (sub_nonpos.mpr hwa)]
    have hroot : Real.sqrt (w + delta) <= Real.sqrt (a + delta) :=
      Real.sqrt_le_sqrt (by linarith)
    have hprod := mul_nonneg hnw (sub_nonneg.mpr hroot)
    nlinarith

theorem overweight_le_repairHellingerEnergy (a w delta : Real)
    (ha : 0 <= a) (hw : 0 <= w) (hd : 0 <= delta) :
    max (w - a) 0 <= 2 * repairHellingerEnergy a w delta +
      if a < w then a + delta else 0 := by
  have hsa := Real.sq_sqrt (add_nonneg ha hd)
  have hsw := Real.sq_sqrt (add_nonneg hw hd)
  by_cases haw : a < w
  case pos =>
    rw [ite_eq_left haw, max_eq_left (sub_nonneg.mpr haw.le)]
    unfold repairHellingerEnergy
    nlinarith [sq_nonneg
      (Real.sqrt (w + delta) - 2 * Real.sqrt (a + delta))]
  case neg =>
    have hwa : w <= a := not_lt.mp haw
    rw [ite_eq_right haw, max_eq_right (sub_nonpos.mpr hwa)]
    have he := repairHellingerEnergy_nonneg a w delta
    linarith

theorem abs_sub_overweight_ledger (a w : Real) :
    abs (w - a) = 2 * max (w - a) 0 + a - w := by
  by_cases haw : a <= w
  case pos =>
    rw [abs_of_nonneg (sub_nonneg.mpr haw),
      max_eq_left (sub_nonneg.mpr haw)]
    linarith
  case neg =>
    have hwa : w <= a := (lt_of_not_ge haw).le
    rw [abs_of_nonpos (sub_nonpos.mpr hwa),
      max_eq_right (sub_nonpos.mpr hwa)]
    linarith

theorem abs_sub_sum_overweight_ledger {I : Type*} (S : Finset I)
    (a w : I -> Real) :
    S.sum (fun i => abs (w i - a i)) =
      2 * S.sum (fun i => max (w i - a i) 0) +
        S.sum a - S.sum w := by
  simp only [abs_sub_overweight_ledger, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem repairHellingerEnergy_sum_le_ledger {I : Type*} (S : Finset I)
    (a w delta : I -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hd : forall i, Membership.mem S i -> 0 <= delta i) :
    S.sum (fun i => repairHellingerEnergy (a i) (w i) (delta i)) <=
      2 * S.sum (fun i => max (w i - a i) 0) +
        S.sum a - S.sum w := by
  calc
    _ <= S.sum (fun i => abs (w i - a i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact repairHellingerEnergy_le_abs (a i) (w i) (delta i)
        (ha i hi) (hw i hi) (hd i hi)
    _ = _ := abs_sub_sum_overweight_ledger S a w

theorem overweight_sum_le_repairHellingerEnergy {I : Type*}
    (S : Finset I) (a w delta : I -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hd : forall i, Membership.mem S i -> 0 <= delta i) :
    S.sum (fun i => max (w i - a i) 0) <=
      2 * S.sum (fun i => repairHellingerEnergy (a i) (w i) (delta i)) +
        S.sum (fun i => if a i < w i then a i + delta i else 0) := by
  calc
    _ <= S.sum (fun i =>
        2 * repairHellingerEnergy (a i) (w i) (delta i) +
          if a i < w i then a i + delta i else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact overweight_le_repairHellingerEnergy (a i) (w i) (delta i)
        (ha i hi) (hw i hi) (hd i hi)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem overweight_sum_le_energy_add_repair_capacity {I : Type*}
    (S : Finset I) (a w delta : I -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hd : forall i, Membership.mem S i -> 0 <= delta i) :
    S.sum (fun i => max (w i - a i) 0) <=
      2 * S.sum (fun i => repairHellingerEnergy (a i) (w i) (delta i)) +
        (S.filter (fun i => a i < w i)).sum (fun i => a i + delta i) := by
  simpa only [Finset.sum_filter] using
    overweight_sum_le_repairHellingerEnergy S a w delta ha hw hd

theorem overweight_sum_le_energy_add_repair_count {I : Type*}
    (S : Finset I) (a w delta : I -> Real) (c : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hd : forall i, Membership.mem S i -> 0 <= delta i)
    (hc : forall i, Membership.mem S i -> a i + delta i <= c) :
    S.sum (fun i => max (w i - a i) 0) <=
      2 * S.sum (fun i => repairHellingerEnergy (a i) (w i) (delta i)) +
        ((S.filter (fun i => a i < w i)).card : Real) * c := by
  have hcap : (S.filter (fun i => a i < w i)).sum (fun i => a i + delta i) <=
      ((S.filter (fun i => a i < w i)).card : Real) * c := by
    calc
      _ <= (S.filter (fun i => a i < w i)).sum (fun _ => c) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hc i (Finset.mem_filter.mp hi).1
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsum := overweight_sum_le_energy_add_repair_capacity S a w delta ha hw hd
  linarith

end PrimeFactorOscillations.PrimeClassDeletion
