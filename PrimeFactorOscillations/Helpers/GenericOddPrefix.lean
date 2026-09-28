import PrimeFactorOscillations.Definitions.OddPrimePrefix
import PrimeFactorOscillations.Helpers.GenericOddOrder
import PrimeFactorOscillations.Helpers.LocalSymmetricRatio
import PrimeFactorOscillations.Helpers.PrimePrefixWeights

set_option autoImplicit false

/-! # Exact treatment of the exceptional prime two in generic odd prefixes -/

namespace PrimeFactorOscillations

/-- A zero local probability contributes no Bernoulli trial or rank shift. -/
theorem finiteLocalMass_cons_zero (eta : Nat -> Rat) (p : Nat) (entries : List Nat)
    (hp : eta p = 0) (r : Nat) :
    finiteLocalMass eta (p :: entries) r = finiteLocalMass eta entries r := by
  cases r <;> simp [finiteLocalMass, hp]

/-- Remove prime two from a prime list without changing any mass coefficient. -/
theorem genericOdd_mass_filter (entries : List Nat)
    (hprime : forall p, List.Mem p entries -> Nat.Prime p) (r : Nat) :
    finiteLocalMass genericOddEta entries r =
      finiteLocalMass genericOddEta (entries.filter (fun p => decide (2 < p))) r := by
  induction entries generalizing r with
  | nil => rfl
  | cons p entries ih =>
      have hp := hprime p (List.Mem.head _)
      have ht : forall q, List.Mem q entries -> Nat.Prime q :=
        fun q hq => hprime q (List.Mem.tail _ hq)
      by_cases hgt : 2 < p
      next =>
        simp only [List.filter_cons, hgt, decide_true, ite_true]
        cases r with
        | zero => simp only [finiteLocalMass, ih ht 0]
        | succ r => simp only [finiteLocalMass, ih ht r, ih ht (r + 1)]
      next =>
        have heq : p = 2 := by have htwo := hp.two_le; omega
        subst p
        rw [finiteLocalMass_cons_zero genericOddEta 2 entries (by simp [genericOddEta]) r]
        simpa using ih ht r

/-- The actual canonical prime-prefix mass equals its strictly positive odd part. -/
theorem genericOdd_prefix_mass_eq (x r : Nat) :
    finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) r =
      finiteLocalMass genericOddEta (oddPrimesBelow x) r := by
  exact genericOdd_mass_filter _
    (fun p hp => (PrimeFactorUnimodality.primesBelow_entries x p hp).1) r

/-- Every entry remaining in the prefix is above two. -/
theorem oddPrimesBelow_gt_two (x p : Nat) (hp : List.Mem p (oddPrimesBelow x)) :
    2 < p := by
  have h := (List.mem_filter.mp hp).2
  exact of_decide_eq_true h

/-- Removing prime two also leaves the total odds sum unchanged. -/
theorem genericOdd_weightSum_filter (entries : List Nat)
    (hprime : forall p, List.Mem p entries -> Nat.Prime p) :
    ((entries.filter (fun p => decide (2 < p))).map genericOddWeight).sum =
      (entries.map genericOddWeight).sum := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
      have hp := hprime p (List.Mem.head _)
      have ht : forall q, List.Mem q entries -> Nat.Prime q :=
        fun q hq => hprime q (List.Mem.tail _ hq)
      by_cases hgt : 2 < p
      next => simp [hgt, ih ht]
      next =>
        have heq : p = 2 := by have htwo := hp.two_le; omega
        subst p
        simpa [genericOddWeight, genericOddEta] using ih ht

/-- The filtered list sum is the already estimated canonical generic odds sum. -/
theorem genericOdd_sum_oddPrimesBelow (x : Nat) :
    ((oddPrimesBelow x).map genericOddWeight).sum = genericOddPrimeWeightSum x := by
  rw [oddPrimesBelow, genericOdd_weightSum_filter _
    (fun p hp => (PrimeFactorUnimodality.primesBelow_entries x p hp).1)]
  exact (genericOddPrimeWeightSum_eq x).symm

/-- All remaining local probabilities lie strictly between zero and one. -/
theorem genericOdd_prefix_probabilities (x p : Nat)
    (hp : List.Mem p (oddPrimesBelow x)) :
    0 < genericOddEta p /\ genericOddEta p < 1 := by
  have hgt := oddPrimesBelow_gt_two x p hp
  exact And.intro (genericOddEta_pos p hgt) (genericOddEta_lt_one p hgt)

/-- The odds on the positive prime prefix are nonincreasing. -/
theorem genericOdd_prefix_odds_descending (x : Nat) :
    ((oddPrimesBelow x).map genericOddWeight).Pairwise (fun a b => b <= a) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem
    (fun {a b} ha _hb hab => genericOddWeight_antitone (oddPrimesBelow_gt_two x a ha) hab)
  exact List.Pairwise.filter (fun p => decide (2 < p))
    (PrimeFactorUnimodality.primesBelow_pairwise_le x)

/-- Positivity at precisely the supported generic odd degrees. -/
theorem genericOdd_prefix_mass_pos (x r : Nat) (hr : r <= (oddPrimesBelow x).length) :
    0 < finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) r := by
  rw [genericOdd_prefix_mass_eq]
  exact local_mass_pos genericOddEta _ (genericOdd_prefix_probabilities x) r hr

/-- The actual generic odd prime-prefix ratio, with the prime-two exception
removed exactly and with no assumed ordering or analytic estimate. -/
theorem genericOdd_prefix_ratio_bounds (x r : Nat) (hrPos : 1 <= r)
    (hr : r <= (oddPrimesBelow x).length)
    (hComplement : 0 < genericOddPrimeWeightSum x -
      (((oddPrimesBelow x).map genericOddWeight).take (r - 1)).sum) :
    (r : Rat) / genericOddPrimeWeightSum x <=
        finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) (r - 1) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) r /\
      finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) (r - 1) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) r <=
        (r : Rat) / (genericOddPrimeWeightSum x -
          (((oddPrimesBelow x).map genericOddWeight).take (r - 1)).sum) := by
  have hc : 0 < ((oddPrimesBelow x).map genericOddWeight).sum -
      (((oddPrimesBelow x).map genericOddWeight).take (r - 1)).sum := by
    rwa [genericOdd_sum_oddPrimesBelow]
  have h := local_densityRatio_bounds genericOddEta (oddPrimesBelow x)
    (genericOdd_prefix_probabilities x) r hrPos hr (genericOdd_prefix_odds_descending x) hc
  rw [genericOdd_prefix_mass_eq, genericOdd_prefix_mass_eq]
  change (r : Rat) / ((oddPrimesBelow x).map genericOddWeight).sum <=
      finiteLocalMass genericOddEta (oddPrimesBelow x) (r - 1) /
        finiteLocalMass genericOddEta (oddPrimesBelow x) r /\
    finiteLocalMass genericOddEta (oddPrimesBelow x) (r - 1) /
        finiteLocalMass genericOddEta (oddPrimesBelow x) r <=
      (r : Rat) / (((oddPrimesBelow x).map genericOddWeight).sum -
        (((oddPrimesBelow x).map genericOddWeight).take (r - 1)).sum) at h
  simpa only [genericOdd_sum_oddPrimesBelow] using h

end PrimeFactorOscillations
