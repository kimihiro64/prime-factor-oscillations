import PrimeFactorOscillations.Definitions.RealLocalDensity
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliOdds

/-! # Exact real density signs at consecutive primes -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- At consecutive primes the next prefix adjoins exactly the earlier prime. -/
theorem prefix_mass_at_next_prime (law : ReciprocalSmoothLaw) (p q r : Nat)
    (hp : Nat.Prime p) (hpq : p < q)
    (hgap : forall t : Nat, p < t -> t < q -> Not (Nat.Prime t)) :
    law.prefixMass q r =
      List.bernoulliMass (law.eta p :: law.prefixProbabilities p) r := by
  have hsets : (Finset.range q).filter Nat.Prime =
      insert p ((Finset.range p).filter Nat.Prime) := by
    apply Finset.ext
    intro t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    next =>
      intro ht
      by_cases heq : t = p
      next => exact Or.inl heq
      next =>
        refine Or.inr (And.intro ?_ ht.2)
        by_contra hn
        exact hgap t (by omega) ht.1 ht.2
    next =>
      intro ht
      rcases ht with heq | hsmall
      next => simpa only [heq] using And.intro hpq hp
      next => exact And.intro (hsmall.1.trans hpq) hsmall.2
  have hnot : Not (Membership.mem ((Finset.range p).filter Nat.Prime) p) := by simp
  have hperm := (Finset.toList_insert hnot).map law.eta
  unfold prefixMass prefixProbabilities
  rw [hsets, List.bernoulliMass_perm hperm]
  rfl

/-- The exact signed difference retains both prime endpoints and the true rank. -/
theorem rank_density_step_difference (law : ReciprocalSmoothLaw) (k p q : Nat)
    (hk : 2 <= k) (hp : Nat.Prime p) (hpq : p < q)
    (hgap : forall t : Nat, p < t -> t < q -> Not (Nat.Prime t))
    (ha : Not (law.eta p = 0)) (hb : Not (law.eta q = 0))
    (hF : Not (law.prefixMass p (k - 1) = 0)) :
    law.rankDensityAt k q - law.rankDensityAt k p =
      (law.eta p * law.eta q * law.prefixMass p (k - 1)) *
        (law.prefixMass p (k - 2) / law.prefixMass p (k - 1) -
          (1 / law.eta q - 1 / law.eta p + 1)) := by
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hF' : Not (List.bernoulliMass (law.prefixProbabilities p) (k - 2 + 1) = 0) := by
    simpa only [hindex, prefixMass] using hF
  have h := List.bernoulliMass_step_difference (law.prefixProbabilities p)
    (law.eta p) (law.eta q) (k - 2) ha hb hF'
  rw [hindex] at h
  unfold rankDensityAt
  rw [law.prefix_mass_at_next_prime p q (k - 1) hp hpq hgap]
  exact h

/-- Exact ascent criterion for the actual real local density. -/
theorem rank_density_ascent_iff (law : ReciprocalSmoothLaw) (k p q : Nat)
    (hk : 2 <= k) (hp : Nat.Prime p) (hpq : p < q)
    (hgap : forall t : Nat, p < t -> t < q -> Not (Nat.Prime t))
    (ha : 0 < law.eta p) (hb : 0 < law.eta q)
    (hF : 0 < law.prefixMass p (k - 1)) :
    law.rankDensityAt k p < law.rankDensityAt k q <->
      1 / law.eta q - 1 / law.eta p + 1 <
        law.prefixMass p (k - 2) / law.prefixMass p (k - 1) := by
  rw [<- sub_pos, law.rank_density_step_difference k p q hk hp hpq hgap
    (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hF)]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos ha hb) hF), sub_pos]

/-- Exact descent criterion for the same consecutive-prime step. -/
theorem rank_density_descent_iff (law : ReciprocalSmoothLaw) (k p q : Nat)
    (hk : 2 <= k) (hp : Nat.Prime p) (hpq : p < q)
    (hgap : forall t : Nat, p < t -> t < q -> Not (Nat.Prime t))
    (ha : 0 < law.eta p) (hb : 0 < law.eta q)
    (hF : 0 < law.prefixMass p (k - 1)) :
    law.rankDensityAt k q < law.rankDensityAt k p <->
      law.prefixMass p (k - 2) / law.prefixMass p (k - 1) <
        1 / law.eta q - 1 / law.eta p + 1 := by
  rw [<- sub_neg, law.rank_density_step_difference k p q hk hp hpq hgap
    (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hF)]
  have hscale := mul_pos (mul_pos ha hb) hF
  constructor
  next =>
    intro h
    by_contra hn
    exact not_lt_of_ge
      (mul_nonneg hscale.le (sub_nonneg.mpr (le_of_not_gt hn))) h
  next =>
    intro h
    exact mul_neg_of_pos_of_neg hscale (sub_neg.mpr h)


end PrimeFactorOscillations.ReciprocalSmoothLaw
