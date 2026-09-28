import PrimeFactorOscillations.Helpers.LocalMassChernoff
import PrimeFactorOscillations.Helpers.OrdinaryLocalLawBridge
import PrimeFactorOscillations.Helpers.WeightSumUpper

set_option autoImplicit false

/-! # Exponential bounds on the actual cumulative rank densities -/

namespace PrimeFactorOscillations

/-- At every prime the generic odd local selection probability is smaller
than the ordinary reciprocal-prime probability, including prime two. -/
theorem genericOddEta_le_reciprocal (p : Nat) (hp : Nat.Prime p) :
    0 <= genericOddEta p /\ genericOddEta p <= 1 / (p : Rat) := by
  by_cases htwo : p = 2
  next =>
    subst p
    norm_num [genericOddEta]
  next =>
    have hpgt : 2 < p := by have h := hp.two_le; omega
    have hpR : (0 : Rat) < p := by exact_mod_cast hp.pos
    have hpos := genericOddEta_pos p hpgt
    have hrec : (p : Rat) <= 1 / genericOddEta p := by
      rw [genericOddEta_reciprocal p hpgt]
      have hpTwo : (2 : Rat) < p := by exact_mod_cast hpgt
      have hd : (0 : Rat) < (p : Rat) - 2 := by linarith only [hpTwo]
      exact le_add_of_nonneg_right (div_nonneg (by norm_num) hd.le)
    have hmul := mul_le_mul_of_nonneg_right hrec hpos.le
    have hcancel : (1 / genericOddEta p) * genericOddEta p = 1 := by
      field_simp [ne_of_gt hpos]
    rw [hcancel] at hmul
    refine And.intro hpos.le ?_
    by_contra h
    have hgt : 1 / (p : Rat) < genericOddEta p := lt_of_not_ge h
    have hgtMul := mul_lt_mul_of_pos_right hgt hpR
    have hc : (1 / (p : Rat)) * p = 1 := by field_simp [ne_of_gt hpR]
    rw [hc] at hgtMul
    nlinarith only [hmul, hgtMul]

/-- The mean of any prime-local law dominated by reciprocal primes has a
uniform logarithmic upper bound. The finite support is exactly primes below n+1. -/
theorem localMean_le_loglog (eta : Nat -> Rat)
    (hbound : forall p, Nat.Prime p -> eta p <= 1 / (p : Rat))
    (n : Nat) (hn : 2 <= n) :
    (((PrimeFactorUnimodality.primesBelow (n + 1)).map eta).sum : Real) <=
      Real.log (Real.log n) + primeWeightLowerConstant := by
  have hs : ((PrimeFactorUnimodality.primesBelow (n + 1)).map eta).sum <=
      ordinaryPrimeWeightSum (n + 1) := by
    rw [sum_primesBelow_eq]
    unfold ordinaryPrimeWeightSum
    apply Finset.sum_le_sum
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    have hpR : (1 : Rat) < p := by exact_mod_cast hprime.one_lt
    apply (hbound p hprime).trans
    rw [ordinaryWeight_cast p hprime.one_lt.le]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  exact ((Rat.cast_le (K := Real)).mpr hs).trans (both_primeWeightSums_upper n hn).2

/-- The exact CDF identity turns the finite Chernoff bound into a statement
about rank densities, without assuming an arithmetic ensemble interpretation. -/
theorem localRankDensity_cumulative_le_exp_of_mean (eta : Nat -> Rat)
    (r n : Nat) (c C : Real)
    (heta : forall p, List.Mem p (PrimeFactorUnimodality.primesBelow
      (PrimeFactorUnimodality.primeAt n)) -> 0 <= eta p /\ eta p <= 1)
    (hmean : (((PrimeFactorUnimodality.primesBelow
        (PrimeFactorUnimodality.primeAt n)).map eta).sum : Real) <=
      c * (r + 1 : Nat) + C) :
    (((Finset.range n).sum (localRankDensity eta (r + 1)) : Rat) : Real) <=
      Real.exp (-(Real.log 3 - 2 * c) * (r + 1 : Nat) + 2 * C) := by
  have h := finiteLocalMass_tail_le_exp_of_mean eta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt n))
    heta (r + 1) c C hmean
  rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at h
  rw [localRankDensity_sum_eq_mass_tail_all]
  exact h

/-- Both actual canonical densities obey the same explicit rare-region bound
at every positive rank and every indicated finite prime prefix. -/
theorem both_density_cumulative_le_exp_of_scale (r n : Nat) (c : Real)
    (hn : 3 <= PrimeFactorUnimodality.primeAt n)
    (hscale : Real.log (Real.log
      ((PrimeFactorUnimodality.primeAt n - 1 : Nat) : Real)) <= c * (r + 1 : Nat)) :
    (((Finset.range n).sum (ordinaryDensity (r + 1)) : Rat) : Real) <=
        Real.exp (-(Real.log 3 - 2 * c) * (r + 1 : Nat) +
          2 * primeWeightLowerConstant) /\
      (((Finset.range n).sum (genericOddDensity (r + 1)) : Rat) : Real) <=
        Real.exp (-(Real.log 3 - 2 * c) * (r + 1 : Nat) +
          2 * primeWeightLowerConstant) := by
  have hmean (eta : Nat -> Rat)
      (hb : forall p, Nat.Prime p -> eta p <= 1 / (p : Rat)) :
      (((PrimeFactorUnimodality.primesBelow
          (PrimeFactorUnimodality.primeAt n)).map eta).sum : Real) <=
        c * (r + 1 : Nat) + primeWeightLowerConstant := by
    have h := localMean_le_loglog eta hb
      (PrimeFactorUnimodality.primeAt n - 1) (by omega)
    rw [Nat.sub_add_cancel (show 1 <= PrimeFactorUnimodality.primeAt n by omega)] at h
    exact h.trans (by linarith only [hscale])
  have hordinaryProb (p : Nat) (hp : Nat.Prime p) :
      0 <= 1 / (p : Rat) /\ 1 / (p : Rat) <= 1 := by
    have hpR : (0 : Rat) < p := by exact_mod_cast hp.pos
    refine And.intro (div_nonneg (by norm_num) hpR.le) ?_
    exact (div_le_one hpR).mpr (by exact_mod_cast hp.one_lt.le)
  have hgenericProb (p : Nat) (hp : Nat.Prime p) :
      0 <= genericOddEta p /\ genericOddEta p <= 1 := by
    have h := genericOddEta_le_reciprocal p hp
    exact And.intro h.1 (h.2.trans (hordinaryProb p hp).2)
  have ho := localRankDensity_cumulative_le_exp_of_mean (fun p => 1 / (p : Rat))
    r n c primeWeightLowerConstant
    (fun p hp => hordinaryProb p
      (PrimeFactorUnimodality.primesBelow_entries _ p hp).1)
    (hmean _ (fun _ _ => le_rfl))
  have hg := localRankDensity_cumulative_le_exp_of_mean genericOddEta
    r n c primeWeightLowerConstant
    (fun p hp => hgenericProb p
      (PrimeFactorUnimodality.primesBelow_entries _ p hp).1)
    (hmean _ (fun p hp => (genericOddEta_le_reciprocal p hp).2))
  refine And.intro ?_ hg
  simpa only [ordinaryDensity_eq_localRankDensity] using ho

end PrimeFactorOscillations
