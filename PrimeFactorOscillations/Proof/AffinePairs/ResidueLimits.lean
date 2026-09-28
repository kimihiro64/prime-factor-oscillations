import PrimeFactorOscillations.Proof.AffinePairs.ResidueCounts

/-! # Actual prime-pair probabilities at a fixed modulus -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem prime_pair_residue_probability_eq_sum (N q : Nat)
    (R : Finset (Prod (ZMod q) (ZMod q))) :
    primePairResidueProbability N q R = R.sum (fun ab =>
      ((Real.primeCountingZMod (N : Real) q ab.1 : Real) / (Nat.primeCounting N : Real)) *
      ((Real.primeCountingZMod (N : Real) q ab.2 : Real) / (Nat.primeCounting N : Real))) := by
  unfold primePairResidueProbability
  rw [prime_pair_residue_count_eq_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [Nat.cast_mul]
  ring

theorem tendsto_prime_pair_residue_probability_sum (q : Nat) (hq : 1 <= q)
    (R : Finset (Prod (ZMod q) (ZMod q))) :
    Filter.Tendsto (fun N : Nat => primePairResidueProbability N q R)
      Filter.atTop (nhds (R.sum (fun ab =>
        (if IsUnit ab.1 then 1 / (q.totient : Real) else 0) *
        (if IsUnit ab.2 then 1 / (q.totient : Real) else 0)))) := by
  have hsum := tendsto_finsetSum R (fun ab _ =>
    (tendsto_all_prime_progression_probabilities q hq ab.1).mul
      (tendsto_all_prime_progression_probabilities q hq ab.2))
  simpa only [<- prime_pair_residue_probability_eq_sum] using hsum

theorem tendsto_prime_pair_residue_probability (q : Nat) (hq : 1 <= q)
    (R : Finset (Prod (ZMod q) (ZMod q))) :
    Filter.Tendsto (fun N : Nat => primePairResidueProbability N q R)
      Filter.atTop (nhds (((R.filter (fun ab => IsUnit ab.1 /\ IsUnit ab.2)).card : Real) /
        (q.totient : Real) ^ 2)) := by
  have hterm : forall ab : Prod (ZMod q) (ZMod q),
      (if IsUnit ab.1 then 1 / (q.totient : Real) else 0) *
        (if IsUnit ab.2 then 1 / (q.totient : Real) else 0) =
      if IsUnit ab.1 /\ IsUnit ab.2 then 1 / (q.totient : Real) ^ 2 else 0 := by
    intro ab
    by_cases ha : IsUnit ab.1 <;> by_cases hb : IsUnit ab.2 <;>
      simp only [ha, hb, and_self, and_false, false_and, ite_true, ite_false,
        mul_zero, zero_mul, div_mul_div_comm, one_mul, pow_two]
  have hsum : R.sum (fun ab =>
      (if IsUnit ab.1 then 1 / (q.totient : Real) else 0) *
      (if IsUnit ab.2 then 1 / (q.totient : Real) else 0)) =
      ((R.filter (fun ab => IsUnit ab.1 /\ IsUnit ab.2)).card : Real) /
        (q.totient : Real) ^ 2 := by
    simp_rw [hterm]
    rw [<- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [<- hsum]
  exact tendsto_prime_pair_residue_probability_sum q hq R

end PrimeFactorOscillations
