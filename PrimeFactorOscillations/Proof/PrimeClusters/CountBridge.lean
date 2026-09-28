import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.WeightedCount
import PrimeFactorOscillations.Proof.PrimeClusters.WeightBound

set_option autoImplicit false

/-! # CountBridge in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem exists_uniform_cluster_moment_count_bound {k : Nat} (hk : 2 <= k)
    (theta delta : Real) (ht : 0 < theta /\ theta < 1)
    (hd : 0 < delta /\ delta < theta / 2) :
    exists C : Real, 0 < C /\ exists N0 : Real,
      forall N : Nat, N0 <= (N : Real) ->
      forall lam : Finsupp (Fin k -> Nat) Real,
        lam.HasPermissibleSupport
          (Nat.floor ((N : Real) ^ (theta / 2 - delta))) (sieveModulus N) ->
      forall h : Fin k -> Nat, forall s : Finset Nat,
        s.sum (fun n =>
            (((Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card : Real) *
              weight h lam n)) -
          s.sum (weight h lam) <=
        ((s.filter (fun n =>
            2 <= (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card)).card :
            Real) *
          (((k : Real) - 1) *
            (C * Finsupp.maxRealAbs (lToY lam) *
              (N : Real) ^ (theta / 2 - delta) *
              Real.log ((N : Real) ^ (theta / 2 - delta)) ^ (2 * k)) ^ 2) := by
  classical
  choose C hC N0 hbound using exists_uniform_weight_bound hk theta delta ht hd
  refine Exists.intro C (And.intro hC (Exists.intro N0 ?_))
  intro N hN lam hlam h s
  apply Finset.weighted_moments_sub_le_card_filter
  next =>
    intro n hn
    exact w_nonneg
  next =>
    intro n hn
    exact hbound N hN lam hlam h n
  next =>
    intro n hn
    exact (Finset.card_filter_le _ _).trans (by simp)

end PrimeGaps
