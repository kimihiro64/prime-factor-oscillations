/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.HamiltonianWeightedReveal

/-! # The full weighted logarithmic reveal estimate

The permanent's matching weights supply the probability measure.
The sequential subprobability retains every available-column factor.
The logarithmic comparison is derived from log(x) <= x - 1,
including zero matching weights without a positivity approximation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {R C L : Type*} [DecidableEq C] [DecidableEq L]

def hamiltonianRevealRowProduct (A : R -> C -> Real) :
    List R -> (R -> C) -> Real
  | [], _ => 1
  | i :: rows, f => A i (f i) * hamiltonianRevealRowProduct A rows f

def hamiltonianRevealLogCost (A : R -> C -> Real) :
    List R -> Finset C -> (R -> C) -> Real
  | [], _, _ => 0
  | i :: rows, available, f =>
      Real.log (available.sum (A i)) +
        hamiltonianRevealLogCost A rows (available.erase (f i)) f

theorem hamiltonian_reveal_row_product_nonnegative (A : R -> C -> Real)
    (hA : forall i j, 0 <= A i j) (rows : List R) (f : R -> C) :
    0 <= hamiltonianRevealRowProduct A rows f := by
  induction rows with
  | nil => norm_num [hamiltonianRevealRowProduct]
  | cons i rows ih => exact mul_nonneg (hA i (f i)) ih

theorem hamiltonian_reveal_positive_log_identity
    (A : R -> C -> Real) (hA : forall i j, 0 <= A i j)
    (rows : List R) (available : Finset C) (f : R -> C)
    (hMap : forall i, Membership.mem rows i -> Membership.mem available (f i))
    (hDistinct : List.Pairwise (fun i j => Not (f i = f j)) rows)
    (hProduct : 0 < hamiltonianRevealRowProduct A rows f) :
    0 < hamiltonianRevealWeight A rows available f /\
      Real.log (hamiltonianRevealWeight A rows available f) =
        Real.log (hamiltonianRevealRowProduct A rows f) -
          hamiltonianRevealLogCost A rows available f := by
  induction rows generalizing available with
  | nil =>
    norm_num [hamiltonianRevealWeight, hamiltonianRevealRowProduct, hamiltonianRevealLogCost]
  | cons i rows ih =>
    have hTailNonneg := hamiltonian_reveal_row_product_nonnegative A hA rows f
    have hHead : 0 < A i (f i) :=
      pos_of_mul_pos_left hProduct hTailNonneg
    have hTail : 0 < hamiltonianRevealRowProduct A rows f :=
      pos_of_mul_pos_right hProduct (hA i (f i))
    have hHeadMem : Membership.mem available (f i) := hMap i (by simp)
    have hTotal : 0 < available.sum (A i) :=
      lt_of_lt_of_le hHead (Finset.single_le_sum (fun j _ => hA i j) hHeadMem)
    have hTailMap : forall k, Membership.mem rows k ->
        Membership.mem (available.erase (f i)) (f k) := by
      intro k hk
      have hNe := (List.pairwise_cons.mp hDistinct).1 k hk
      exact Finset.mem_erase.mpr (And.intro (Ne.symm hNe)
        (hMap k (List.mem_cons_of_mem i hk)))
    have hChild := ih (available.erase (f i)) hTailMap
      (List.pairwise_cons.mp hDistinct).2 hTail
    have hQuotient : 0 < A i (f i) / available.sum (A i) := div_pos hHead hTotal
    refine And.intro (mul_pos hQuotient hChild.1) ?_
    simp only [hamiltonianRevealWeight, hamiltonianRevealRowProduct, hamiltonianRevealLogCost]
    rw [Real.log_mul (ne_of_gt hQuotient) (ne_of_gt hChild.1),
      Real.log_div (ne_of_gt hHead) (ne_of_gt hTotal),
      Real.log_mul (ne_of_gt hHead) (ne_of_gt hTail), hChild.2]
    ring

theorem hamiltonian_finite_log_partition_bound
    (s : Finset L) (w q cost : L -> Real)
    (hW : forall z, Membership.mem s z -> 0 <= w z)
    (hQ : forall z, Membership.mem s z -> 0 <= q z)
    (hQSum : s.sum q <= 1) (hMass : 0 < s.sum w)
    (hPositive : forall z, Membership.mem s z -> 0 < w z -> 0 < q z)
    (hLog : forall z, Membership.mem s z -> 0 < w z ->
      Real.log (q z) = Real.log (w z) - cost z) :
    Real.log (s.sum w) <= s.sum (fun z => w z * cost z) / s.sum w := by
  let P := s.sum w
  have hP : 0 < P := hMass
  have hEach (z : L) (hz : Membership.mem s z) :
      w z * (Real.log P - cost z) <= q z * P - w z := by
    by_cases hZero : w z = 0
    case pos =>
      rw [hZero, zero_mul, sub_zero]
      exact mul_nonneg (hQ z hz) (le_of_lt hP)
    case neg =>
      have hw : 0 < w z := lt_of_le_of_ne (hW z hz) (Ne.symm hZero)
      have hq : 0 < q z := hPositive z hz hw
      have hArg : 0 < q z * P / w z := div_pos (mul_pos hq hP) hw
      have hBound := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos hArg) (le_of_lt hw)
      rw [Real.log_div (ne_of_gt (mul_pos hq hP)) (ne_of_gt hw),
        Real.log_mul (ne_of_gt hq) (ne_of_gt hP), hLog z hz hw] at hBound
      have hClear : w z * (q z * P / w z - 1) = q z * P - w z := by
        field_simp [hZero]
      rw [hClear] at hBound
      nlinarith only [hBound]
  have hSum := Finset.sum_le_sum hEach
  have hLeft : s.sum (fun z => w z * (Real.log P - cost z)) =
      P * Real.log P - s.sum (fun z => w z * cost z) := by
    simp only [mul_sub, Finset.sum_sub_distrib, <- Finset.sum_mul, P]
  have hRight : s.sum (fun z => q z * P - w z) = s.sum q * P - P := by
    simp only [Finset.sum_sub_distrib, <- Finset.sum_mul, P]
  rw [hLeft, hRight] at hSum
  have hTotal := mul_le_mul_of_nonneg_right hQSum (le_of_lt hP)
  have hClear : (s.sum (fun z => w z * cost z) / P) * P =
      s.sum (fun z => w z * cost z) := by field_simp [ne_of_gt hP]
  apply le_of_mul_le_mul_right _ hMass
  change Real.log P * P <= (s.sum (fun z => w z * cost z) / P) * P
  rw [hClear]
  nlinarith only [hSum, hTotal]

theorem hamiltonian_reveal_log_partition_bound
    (A : R -> C -> Real) (hA : forall i j, 0 <= A i j)
    (rows : List R) (available : Finset C) (s : Finset L) (f : L -> R -> C)
    (hMap : forall z, Membership.mem s z -> forall i, Membership.mem rows i ->
      Membership.mem available (f z i))
    (hDistinct : forall z, Membership.mem s z ->
      List.Pairwise (fun i j => Not (f z i = f z j)) rows)
    (hSeparate : forall z, Membership.mem s z -> forall w, Membership.mem s w ->
      (forall i, Membership.mem rows i -> f z i = f w i) -> z = w)
    (hMass : 0 < s.sum (fun z => hamiltonianRevealRowProduct A rows (f z))) :
    Real.log (s.sum (fun z => hamiltonianRevealRowProduct A rows (f z))) <=
      s.sum (fun z => hamiltonianRevealRowProduct A rows (f z) *
        hamiltonianRevealLogCost A rows available (f z)) /
      s.sum (fun z => hamiltonianRevealRowProduct A rows (f z)) := by
  apply hamiltonian_finite_log_partition_bound s
    (fun z => hamiltonianRevealRowProduct A rows (f z))
    (fun z => hamiltonianRevealWeight A rows available (f z))
    (fun z => hamiltonianRevealLogCost A rows available (f z))
  case hW => exact fun z _ => hamiltonian_reveal_row_product_nonnegative A hA rows (f z)
  case hQ => exact fun z _ => hamiltonian_reveal_weight_nonnegative A hA rows available (f z)
  case hQSum => exact hamiltonian_reveal_family_subprobability A hA rows available s f hMap hDistinct hSeparate
  case hMass => exact hMass
  case hPositive =>
    intro z hz hw
    exact (hamiltonian_reveal_positive_log_identity A hA rows available (f z)
      (hMap z hz) (hDistinct z hz) hw).1
  case hLog =>
    intro z hz hw
    exact (hamiltonian_reveal_positive_log_identity A hA rows available (f z)
      (hMap z hz) (hDistinct z hz) hw).2

end PrimeFactorOscillations
