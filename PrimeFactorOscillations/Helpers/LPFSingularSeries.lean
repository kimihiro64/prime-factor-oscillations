/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import PrimeFactorOscillations.Helpers.LPFSingularTail

/-!
Convergence and uniform truncation of the actual signed singular coefficient.
All assertions about summability require a positive target t. The zero
coefficient at modulus zero is an explicit convention, not a local law.
The finite partial sum is bounded uniformly in P by 17*tau(t).
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpfRamanujanCoefficient_zero (t : Nat) : lpfRamanujanCoefficient 0 t = 0 := by
  simp [lpfRamanujanCoefficient]

theorem lpfRamanujanCoefficient_one (t : Nat) : lpfRamanujanCoefficient 1 t = 1 := by
  rw [lpfRamanujanCoefficient_eq, lpfRamanujanSum_divisors]
  simp [lpfRationalCoefficient]

noncomputable def lpfSingularPartial (P t : Nat) : Complex :=
  Finset.sum (Finset.range (P + 1)) (fun q => lpfRamanujanCoefficient q t)

noncomputable def lpfSingularSeries (t : Nat) : Complex :=
  tsum (fun q => lpfRamanujanCoefficient q t)

theorem norm_lpfSingularPartial_le (P t : Nat) (ht : 0 < t) :
    norm (lpfSingularPartial P t) <= 17 * (t.divisors.card : Real) := by
  have hCard : 0 < t.divisors.card := Finset.card_pos.mpr
    (Exists.intro 1 (Nat.mem_divisors.mpr (And.intro (one_dvd t) (Nat.ne_of_gt ht))))
  have hTau : (1 : Real) <= (t.divisors.card : Real) := by exact_mod_cast (show 1 <= t.divisors.card by omega)
  by_cases hP : P = 0
  . subst P
    simp [lpfSingularPartial, lpfRamanujanCoefficient_zero]
  . have hP1 : 1 <= P := Nat.pos_of_ne_zero hP
    have hSet : Finset.range (P + 1) = insert 0 (insert 1 (Finset.Ioc 1 P)) := by
      apply Finset.ext
      intro q
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hZero : Not (Membership.mem (insert 1 (Finset.Ioc 1 P)) 0) := by simp
    have hOne : Not (Membership.mem (Finset.Ioc 1 P) 1) := by simp
    have hTail := lpfRamanujanCoefficient_absolute_tail 1 P t (by decide) ht
    simp only [Nat.cast_one, Real.sqrt_one, div_one] at hTail
    calc
      _ <= Finset.sum (Finset.range (P + 1)) (fun q => norm (lpfRamanujanCoefficient q t)) := norm_sum_le _ _
      _ = 1 + Finset.sum (Finset.Ioc 1 P) (fun q => norm (lpfRamanujanCoefficient q t)) := by
        rw [hSet]
        simp only [Finset.sum_insert hZero, Finset.sum_insert hOne,
          lpfRamanujanCoefficient_zero, lpfRamanujanCoefficient_one, norm_zero, norm_one, zero_add]
      _ <= _ := by linarith

theorem lpfRamanujanCoefficient_summable (t : Nat) (ht : 0 < t) :
    Summable (fun q => lpfRamanujanCoefficient q t) := by
  let S : Real := Finset.sum t.divisors (fun d => (d : Real))
  have hRes : forall q, lpfDivisorResonance t q <= S := by
    intro q
    apply Finset.sum_le_sum
    intro d hd
    split_ifs <;> simp <;> positivity
  have hDom : forall q, norm (lpfRamanujanCoefficient q t) <= 4 * S / (q : Real) ^ (3 / 2 : Real) := by
    intro q
    by_cases hq : q = 0
    . subst q; simp [lpfRamanujanCoefficient_zero]
    . have hqPos : 0 < q := Nat.pos_of_ne_zero hq
      exact (norm_lpfRamanujanCoefficient_le q t hqPos ht).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hRes q) (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have hBase : Summable (fun q : Nat => 1 / (q : Real) ^ (3 / 2 : Real)) := by
    simpa only [one_div] using (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : Real) < 3 / 2))
  have hMajorant : Summable (fun q : Nat => 4 * S / (q : Real) ^ (3 / 2 : Real)) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hBase.mul_left (4 * S)
  exact Summable.of_norm_bounded hMajorant hDom

theorem lpfRamanujanCoefficient_shifted_absolute_tail (P L t : Nat) (hP : 1 <= P) (ht : 0 < t) :
    Finset.sum (Finset.range L) (fun i => norm (lpfRamanujanCoefficient (P + 1 + i) t)) <=
      16 * (t.divisors.card : Real) / Real.sqrt (P : Real) := by
  have hMap : Finset.sum (Finset.range L) (fun i => norm (lpfRamanujanCoefficient (P + 1 + i) t)) =
      Finset.sum (Finset.Ioc P (P + L)) (fun q => norm (lpfRamanujanCoefficient q t)) := by
    apply Finset.sum_bij (fun i _ => P + 1 + i)
    . intro i hi
      apply Finset.mem_Ioc.mpr
      have h := Finset.mem_range.mp hi
      omega
    . intro i hi j hj hEq
      exact Nat.add_left_cancel hEq
    . intro q hq
      have h := Finset.mem_Ioc.mp hq
      let i := q - P - 1
      refine Exists.intro i (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr; dsimp [i]; omega
      . dsimp [i]; omega
    . intro i hi
      rfl
  rw [hMap]
  exact lpfRamanujanCoefficient_absolute_tail P (P + L) t hP ht

theorem norm_lpfRamanujanCoefficient_tsum_tail (P t : Nat) (hP : 1 <= P) (ht : 0 < t) :
    norm (tsum (fun i => lpfRamanujanCoefficient (P + 1 + i) t)) <=
      16 * (t.divisors.card : Real) / Real.sqrt (P : Real) := by
  have hSum : Summable (fun i => lpfRamanujanCoefficient (P + 1 + i) t) :=
    (lpfRamanujanCoefficient_summable t ht).comp_injective (fun i j h => Nat.add_left_cancel h)
  have hFinite : forall L, norm (Finset.sum (Finset.range L)
      (fun i => lpfRamanujanCoefficient (P + 1 + i) t)) <=
        16 * (t.divisors.card : Real) / Real.sqrt (P : Real) := by
    intro L
    exact (norm_sum_le _ _).trans (lpfRamanujanCoefficient_shifted_absolute_tail P L t hP ht)
  exact le_of_tendsto hSum.hasSum.tendsto_sum_nat.norm (Filter.Eventually.of_forall hFinite)

theorem norm_lpfSingularSeries_sub_partial_le (P t : Nat) (hP : 1 <= P) (ht : 0 < t) :
    norm (lpfSingularSeries t - lpfSingularPartial P t) <=
      16 * (t.divisors.card : Real) / Real.sqrt (P : Real) := by
  have hDecomp := (lpfRamanujanCoefficient_summable t ht).sum_add_tsum_nat_add (P + 1)
  have hEq : lpfSingularSeries t - lpfSingularPartial P t =
      tsum (fun i => lpfRamanujanCoefficient (P + 1 + i) t) := by
    unfold lpfSingularSeries lpfSingularPartial
    exact sub_eq_iff_eq_add.mpr (by simpa only [Nat.add_comm, add_comm] using hDecomp.symm)
  rw [hEq]
  exact norm_lpfRamanujanCoefficient_tsum_tail P t hP ht

end PrimeFactorOscillations.LPF
