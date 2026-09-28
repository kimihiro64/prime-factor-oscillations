import PrimeFactorOscillations.Helpers.LocalMassGenerating
import PrimeFactorOscillations.Helpers.LocalMassPermutation
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

/-! # Exact finite cumulative local-rank densities -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Adjoining one entry decreases the probability of having fewer than r+1
selected entries by exactly its rank-(r+1) first-hit mass. -/
theorem finiteLocalMass_sum_range_succ_cons (eta : Nat -> Rat) (xs : List Nat)
    (p r : Nat) :
    (Finset.range (r + 1)).sum (finiteLocalMass eta (p :: xs)) =
      (Finset.range (r + 1)).sum (finiteLocalMass eta xs) -
        eta p * finiteLocalMass eta xs r := by
  rw [Finset.sum_range_succ']
  simp only [finiteLocalMass]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  have hs := Finset.sum_range_succ' (finiteLocalMass eta xs) r
  have hl := Finset.sum_range_succ (finiteLocalMass eta xs) r
  have hsMul := congrArg (fun t : Rat => (1 - eta p) * t) hs
  have hlMul := congrArg (fun t : Rat => eta p * t) hl
  nlinarith only [hsMul, hlMul]

/-- Exact finite CDF identity for the actual canonical local-rank sequence.
The input law is arbitrary; positivity is needed only for its probability interpretation. -/
theorem localRankDensity_sum_range (eta : Nat -> Rat) (r n : Nat) :
    (Finset.range n).sum (localRankDensity eta (r + 1)) =
      1 - (Finset.range (r + 1)).sum
        (finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
          (PrimeFactorUnimodality.primeAt n))) := by
  induction n with
  | zero =>
      have hnil : PrimeFactorUnimodality.primesBelow
          (PrimeFactorUnimodality.primeAt 0) = [] := by
        have hlen := PrimeFactorUnimodality.primesBelow_primeAt_length 0
        cases hxs : PrimeFactorUnimodality.primesBelow
            (PrimeFactorUnimodality.primeAt 0) with
        | nil => rfl
        | cons p ps => simp [hxs] at hlen
      simp [hnil, Finset.sum_range_succ', finiteLocalMass]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hprefix (j : Nat) :
          finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
            (PrimeFactorUnimodality.primeAt (n + 1))) j =
          finiteLocalMass eta (PrimeFactorUnimodality.primeAt n ::
            PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt n)) j :=
        finiteLocalMass_perm eta _ _
          (PrimeFactorUnimodality.primesBelow_primeAt_succ_perm n) j
      simp_rw [hprefix]
      rw [finiteLocalMass_sum_range_succ_cons]
      simp only [localRankDensity, Nat.add_sub_cancel]
      ring

/-- The finite rank CDF is exactly the upper tail of the number selected in
that same prime prefix. The explicit support condition is n+1>=r+1. -/
theorem localRankDensity_sum_eq_mass_tail (eta : Nat -> Rat) (r n : Nat)
    (hr : r <= n) :
    (Finset.range n).sum (localRankDensity eta (r + 1)) =
      ((Finset.range (n + 1)).filter (fun j => r + 1 <= j)).sum
        (finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
          (PrimeFactorUnimodality.primeAt n))) := by
  let mass := finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
    (PrimeFactorUnimodality.primeAt n))
  have hlen := PrimeFactorUnimodality.primesBelow_primeAt_length n
  have htotal := finiteLocalMass_generating eta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt n)) 1
  have htotal' : (Finset.range (n + 1)).sum mass = 1 := by
    simpa [mass, hlen] using htotal
  have hlow :
      (Finset.range (n + 1)).filter (fun j => Not (r + 1 <= j)) =
        Finset.range (r + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) (fun j => r + 1 <= j) mass
  rw [hlow, htotal'] at hpartition
  rw [localRankDensity_sum_range]
  change 1 - (Finset.range (r + 1)).sum mass = _
  linarith only [hpartition]

/-- The exact CDF/tail identity also includes ranks beyond the available
prefix, where both sides vanish. -/
theorem localRankDensity_sum_eq_mass_tail_all (eta : Nat -> Rat) (r n : Nat) :
    (Finset.range n).sum (localRankDensity eta (r + 1)) =
      ((Finset.range (n + 1)).filter (fun j => r + 1 <= j)).sum
        (finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
          (PrimeFactorUnimodality.primeAt n))) := by
  by_cases hr : r <= n
  next => exact localRankDensity_sum_eq_mass_tail eta r n hr
  next =>
    calc
      (Finset.range n).sum (localRankDensity eta (r + 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hin := Finset.mem_range.mp hi
        have hlen : (PrimeFactorUnimodality.primesBelow
            (PrimeFactorUnimodality.primeAt i)).length < r := by
          rw [PrimeFactorUnimodality.primesBelow_primeAt_length]
          omega
        simp only [localRankDensity, Nat.add_sub_cancel,
          finiteLocalMass_eq_zero_of_length_lt eta _ r hlen, mul_zero]
      _ = ((Finset.range (n + 1)).filter (fun j => r + 1 <= j)).sum
          (finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
            (PrimeFactorUnimodality.primeAt n))) := by
        symm
        apply Finset.sum_eq_zero
        intro j hj
        have hfilter := Finset.mem_filter.mp hj
        have hrange := Finset.mem_range.mp hfilter.1
        omega

end PrimeFactorOscillations
