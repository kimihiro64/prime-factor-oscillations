import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

/-! # Adjacent original prime indices inside a prime window -/

namespace PrimeFactorUnimodality

/-- A window containing two primes contains an adjacent pair of indexed primes. -/
theorem exists_adjacent_primes_in_window {n H : Nat}
    (hcount : 2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) :
    exists i, n <= primeAt i /\ primeAt (i + 1) <= n + H := by
  classical
  let S := (Finset.Icc n (n + H)).filter Nat.Prime
  have hcard : 1 < S.card := by
    change 2 <= S.card at hcount
    omega
  choose p q hpq using Finset.one_lt_card_iff.mp hcard
  have hpair : forall a b, Membership.mem S a -> Membership.mem S b -> a < b ->
      exists i, n <= primeAt i /\ primeAt (i + 1) <= n + H := by
    intro a b ha hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have heq := primeAt_primeCounting' a ha'.2
    have hnext : primeAt (Nat.primeCounting' a + 1) <= b := by
      apply (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hb'.2).2
      change primeAt (Nat.primeCounting' a) < b
      rw [heq]
      exact hab
    refine Exists.intro (Nat.primeCounting' a) (And.intro ?_ ?_)
    next =>
      rw [heq]
      exact (Finset.mem_Icc.mp ha'.1).1
    next =>
      exact hnext.trans (Finset.mem_Icc.mp hb'.1).2
  rcases lt_or_gt_of_ne hpq.2.2 with hlt | hgt
  next => exact hpair p q hpq.1 hpq.2.1 hlt
  next => exact hpair q p hpq.2.1 hpq.1 hgt

end PrimeFactorUnimodality
