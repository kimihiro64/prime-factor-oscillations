import PrimeFactorOscillations.Helpers.GenericOddPrefix
import PrimeFactorOscillations.Helpers.LocalFirstDifference
import PrimeFactorOscillations.Helpers.LocalMassPermutation
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

set_option autoImplicit false

/-! # Exact canonical prime steps and the odd-prime threshold margin -/

namespace PrimeFactorOscillations

/-- The sorted next-prime prefix can be replaced by adjoining the current prime. -/
theorem genericOdd_density_succ (k i : Nat) :
    genericOddDensity k (i + 1) =
      genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) *
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primeAt i ::
            PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) := by
  rw [genericOddDensity, localRankDensity]
  rw [finiteLocalMass_perm genericOddEta _ _
    (PrimeFactorUnimodality.primesBelow_primeAt_succ_perm i) (k - 1)]

/-- The exact reciprocal threshold for the actual indexed generic density. -/
theorem genericOdd_density_step_lt_iff (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hdegree : k - 1 <= (oddPrimesBelow (PrimeFactorUnimodality.primeAt i)).length) :
    genericOddDensity k (i + 1) < genericOddDensity k i <->
      finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <
      1 / genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / genericOddEta (PrimeFactorUnimodality.primeAt i) + 1 := by
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) :=
    hp.trans (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i))
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hF : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2 + 1) := by
    rw [hindex]
    exact genericOdd_prefix_mass_pos _ _ hdegree
  have h := localStep_lt_iff genericOddEta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2)
    (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1))
    (genericOddEta_pos _ hp) (genericOddEta_pos _ hq) hF
  rw [genericOdd_density_succ]
  simpa only [genericOddDensity, localRankDensity, hindex] using h

/-- Distinct consecutive primes above two are separated by at least two. -/
theorem primeAt_gap_ge_two (i : Nat) (hp : 2 < PrimeFactorUnimodality.primeAt i) :
    PrimeFactorUnimodality.primeAt i + 2 <= PrimeFactorUnimodality.primeAt (i + 1) := by
  have hlt : PrimeFactorUnimodality.primeAt i < PrimeFactorUnimodality.primeAt (i + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) := hp.trans hlt
  have hpmod := (PrimeFactorUnimodality.prime_primeAt i).eq_two_or_odd.resolve_left (ne_of_gt hp)
  have hqmod := (PrimeFactorUnimodality.prime_primeAt (i + 1)).eq_two_or_odd.resolve_left (ne_of_gt hq)
  omega

/-- Natural prime-gap form consumed by the original ordinary step criterion. -/
theorem primeGap_ge_two (i : Nat) (hp : 2 < PrimeFactorUnimodality.primeAt i) :
    2 <= PrimeFactorUnimodality.primeGap i := by
  have h := primeAt_gap_ge_two i hp
  unfold PrimeFactorUnimodality.primeGap
  omega

/-- Retain the exact decaying correction in the generic odd threshold. -/
theorem genericOdd_threshold_lower (p q : Nat) (hp : 2 < p) (hgap : p + 2 <= q) :
    (3 : Rat) - 1 / ((p : Rat) - 2) <=
      1 / genericOddEta q - 1 / genericOddEta p + 1 := by
  have hq : 2 < q := by omega
  rw [genericOddEta_reciprocal q hq, genericOddEta_reciprocal p hp]
  have hgapR : (p : Rat) + 2 <= (q : Rat) := by exact_mod_cast hgap
  have hqR : (2 : Rat) < (q : Rat) := by exact_mod_cast hq
  have hnonneg : (0 : Rat) <= 1 / ((q : Rat) - 2) :=
    div_nonneg (by norm_num) (by linarith)
  linarith

end PrimeFactorOscillations
