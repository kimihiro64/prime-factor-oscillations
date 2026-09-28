import Mathlib.Tactic.Choose
import PrimeGapsTheory.Sieve.S1.Expansion
import PrimeGapsTheory.Sieve.Sums

set_option autoImplicit false

/-! # WeightBound in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem weight_le_support_l1_sq {k : Nat} (h : Fin k -> Nat)
    (lam : Finsupp (Fin k -> Nat) Real) (n : Nat) :
    weight h lam n <= (lam.support.sum (fun d => abs (lam d))) ^ 2 := by
  classical
  let D := Fintype.piFinset (fun i => (n + h i).divisors)
  have hfilter : D.sum (fun d => abs (lam d)) =
      (D.filter (fun d => Not (lam d = 0))).sum (fun d => abs (lam d)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hz : lam d = 0 <;> simp [hz]
  have hsub : D.filter (fun d => Not (lam d = 0)) <= lam.support := by
    intro d hd
    exact Finsupp.mem_support_iff.mpr (Finset.mem_filter.mp hd).2
  have hsum : D.sum (fun d => abs (lam d)) <=
      lam.support.sum (fun d => abs (lam d)) := by
    rw [hfilter]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg _)
  have hnonneg : 0 <= lam.support.sum (fun d => abs (lam d)) :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  unfold weight
  apply sq_le_sq.mpr
  rw [abs_of_nonneg hnonneg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hsum

theorem exists_uniform_weight_bound {k : Nat} (hk : 2 <= k)
    (theta delta : Real) (ht : 0 < theta /\ theta < 1)
    (hd : 0 < delta /\ delta < theta / 2) :
    exists C : Real, 0 < C /\ exists N0 : Real,
      forall N : Nat, N0 <= (N : Real) ->
      forall lam : Finsupp (Fin k -> Nat) Real,
        lam.HasPermissibleSupport
          (Nat.floor ((N : Real) ^ (theta / 2 - delta))) (sieveModulus N) ->
      forall h : Fin k -> Nat, forall n : Nat,
        weight h lam n <=
          (C * Finsupp.maxRealAbs (lToY lam) *
            (N : Real) ^ (theta / 2 - delta) *
            Real.log ((N : Real) ^ (theta / 2 - delta)) ^ (2 * k)) ^ 2 := by
  classical
  choose C hC N0 hbound using
    GPYSieveS1.lem_l1_bound hk theta delta ht hd
  refine Exists.intro C (And.intro hC (Exists.intro N0 ?_))
  intro N hN lam hlam h n
  have hb := hbound N hN lam hlam lam.support
    (fun d hd => Finsupp.mem_support_iff.mpr hd)
  have hnonneg : 0 <= lam.support.sum (fun d => abs (lam d)) :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hrhs := hnonneg.trans hb
  apply (weight_le_support_l1_sq h lam n).trans
  apply sq_le_sq.mpr
  rw [abs_of_nonneg hnonneg, abs_of_nonneg hrhs]
  exact hb

end PrimeGaps
