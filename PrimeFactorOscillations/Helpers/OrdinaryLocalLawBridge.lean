import PrimeFactorOscillations.Helpers.LocalRankCdf

/-! # Ordinary-density identification with the reciprocal local law -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Match the imported integer-divisibility recurrence, retaining its natural
subtraction convention and the necessary positive-entry condition. -/
theorem reciprocal_localMass_eq_finiteDensity (xs : List Nat)
    (hpos : forall p, List.Mem p xs -> 1 <= p) (r : Nat) :
    finiteLocalMass (fun p => 1 / (p : Rat)) xs r =
      PrimeFactorUnimodality.finiteDensity xs r := by
  induction xs generalizing r with
  | nil => cases r <;> rfl
  | cons p xs ih =>
      have hp := hpos p (List.Mem.head _)
      have ht : forall q, List.Mem q xs -> 1 <= q :=
        fun q hq => hpos q (List.Mem.tail _ hq)
      have hpR : (0 : Rat) < p := by exact_mod_cast (show 0 < p by omega)
      have hcoef : (1 : Rat) - 1 / (p : Rat) = ((p - 1 : Nat) : Rat) / p := by
        rw [Nat.cast_sub hp, Nat.cast_one]
        field_simp [ne_of_gt hpR]
      cases r with
      | zero =>
          rw [finiteLocalMass, PrimeFactorUnimodality.finiteDensity.eq_3,
            ih ht 0, hcoef]
      | succ r =>
          rw [finiteLocalMass, PrimeFactorUnimodality.finiteDensity.eq_4,
            ih ht (r + 1), ih ht r, hcoef]

/-- The canonical ordinary density is exactly the reciprocal-prime local law. -/
theorem ordinaryDensity_eq_localRankDensity (k i : Nat) :
    ordinaryDensity k i =
      localRankDensity (fun p => 1 / (p : Rat)) k i := by
  have hp : forall p, List.Mem p (PrimeFactorUnimodality.primesBelow
      (PrimeFactorUnimodality.primeAt i)) -> 1 <= p := by
    intro p hp
    exact (PrimeFactorUnimodality.primesBelow_entries
      (PrimeFactorUnimodality.primeAt i) p hp).1.one_lt.le
  unfold ordinaryDensity PrimeFactorUnimodality.primeFactorDensity
    PrimeFactorUnimodality.prescribedFactorDensity localRankDensity
  rw [reciprocal_localMass_eq_finiteDensity _ hp]
  ring

/-- Exact CDF for the imported ordinary density, at every positive rank
and finite canonical prime prefix. -/
theorem ordinaryDensity_sum_eq_mass_tail (r n : Nat) :
    (Finset.range n).sum (ordinaryDensity (r + 1)) =
      ((Finset.range (n + 1)).filter (fun j => r + 1 <= j)).sum
        (finiteLocalMass (fun p => 1 / (p : Rat))
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt n))) := by
  calc
    _ = (Finset.range n).sum (localRankDensity (fun p => 1 / (p : Rat)) (r + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ordinaryDensity_eq_localRankDensity (r + 1) i
    _ = _ := localRankDensity_sum_eq_mass_tail_all (fun p => 1 / (p : Rat)) r n

end PrimeFactorOscillations
