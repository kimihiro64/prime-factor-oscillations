/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.TiltedAscentCount

/-!
# Exact excess and deficit on a finite tilt grid

Both event sets retain the inclusive finite grid and strict density test.
Their signed cardinality is exactly actual minus reference. Summed rounding
errors are bounded by the number of selected pairs, with no sign discarded.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

def tiltExcessSet (H M : Nat) (R U g : Real) : Finset Nat :=
  (tiltAscentSet H M R g) \ (tiltAscentSet H M U g)

theorem mem_tiltExcessSet_iff (H M j : Nat) (R U g : Real) :
    Membership.mem (tiltExcessSet H M R U g) j <->
      j < H * M + 1 /\ U <= g + 1 + (j : Real) / M /\
        g + 1 + (j : Real) / M < R := by
  classical
  simp only [tiltExcessSet, Finset.mem_sdiff, tiltAscentSet,
    Finset.mem_filter, Finset.mem_range]
  constructor
  . intro h
    refine And.intro h.1.1 (And.intro ?_ h.1.2)
    exact le_of_not_gt (fun hu => h.2 (And.intro h.1.1 hu))
  . intro h
    exact And.intro (And.intro h.1 h.2.2)
      (fun hu => (not_lt_of_ge h.2.1) hu.2)

theorem tiltAscentCount_sub_eq_excess_sub_deficit
    (H M : Nat) (R U g : Real) :
    ((tiltAscentSet H M R g).card : Real) -
        ((tiltAscentSet H M U g).card : Real) =
      ((tiltExcessSet H M R U g).card : Real) -
        ((tiltExcessSet H M U R g).card : Real) := by
  classical
  have hR := Finset.card_sdiff_add_card_inter
    (tiltAscentSet H M R g) (tiltAscentSet H M U g)
  have hU := Finset.card_sdiff_add_card_inter
    (tiltAscentSet H M U g) (tiltAscentSet H M R g)
  rw [Finset.inter_comm (tiltAscentSet H M U g)] at hU
  have hRc := congrArg (fun n : Nat => (n : Real)) hR
  have hUc := congrArg (fun n : Nat => (n : Real)) hU
  simp only [Nat.cast_add] at hRc hUc
  dsimp only [tiltExcessSet]
  linarith

theorem tiltAscentCount_sum_signed_error_le {I : Type*} (s : Finset I)
    (H M : Nat) (hM : 0 < M) (R U g : I -> Real)
    (hRLow : forall i, Membership.mem s i -> 1 <= R i - g i)
    (hRHigh : forall i, Membership.mem s i -> R i - g i <= (H : Real) + 1)
    (hULow : forall i, Membership.mem s i -> 1 <= U i - g i)
    (hUHigh : forall i, Membership.mem s i -> U i - g i <= (H : Real) + 1) :
    abs (Finset.sum s (fun i =>
        ((tiltExcessSet H M (R i) (U i) (g i)).card : Real) -
          ((tiltExcessSet H M (U i) (R i) (g i)).card : Real)) -
      (M : Real) * Finset.sum s (fun i => R i - U i)) <= s.card := by
  have heq : Finset.sum s (fun i =>
      ((tiltExcessSet H M (R i) (U i) (g i)).card : Real) -
        ((tiltExcessSet H M (U i) (R i) (g i)).card : Real)) -
      (M : Real) * Finset.sum s (fun i => R i - U i) =
      Finset.sum s (fun i => ((tiltAscentSet H M (R i) (g i)).card : Real) -
        ((tiltAscentSet H M (U i) (g i)).card : Real) - (M : Real) * (R i - U i)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [tiltAscentCount_sub_eq_excess_sub_deficit]
  rw [heq]
  calc
    _ <= Finset.sum s (fun i => abs (((tiltAscentSet H M (R i) (g i)).card : Real) -
      ((tiltAscentSet H M (U i) (g i)).card : Real) - (M : Real) * (R i - U i))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum s (fun _ => (1 : Real)) := Finset.sum_le_sum (fun i hi =>
      (tiltAscentSet_signed_error_lt_one H M hM (R i) (U i) (g i)
        (hRLow i hi) (hRHigh i hi) (hULow i hi) (hUHigh i hi)).le)
    _ = _ := by simp

end PrimeFactorOscillations

