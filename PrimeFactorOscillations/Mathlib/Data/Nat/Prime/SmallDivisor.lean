/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Squarefree
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.BalancedProduct

/-!
# Small divisors retaining many prime factors

Specialize the balanced-product partition to the distinct prime factors of a
squarefree natural. This compresses a divisor moment to divisors below the
square root without selecting any particular numerical integer.
-/

set_option autoImplicit false

namespace Nat

/-- A squarefree natural has a divisor below its square root containing
at least half of its distinct prime factors, rounded down. -/
theorem exists_dvd_sq_le_and_primeFactors_card {n : Nat} (hn : Squarefree n) :
    Exists (fun d : Nat => And (Dvd.dvd d n)
      (And (d ^ 2 <= n) (n.primeFactors.card <= 2 * d.primeFactors.card + 1))) := by
  have hfull : n.primeFactors.prod id = n := prod_primeFactors_of_squarefree hn
  cases Finset.exists_subset_sq_prod_le_and_card n.primeFactors id with
  | intro t ht =>
    have hpf : (t.prod id).primeFactors = t :=
      primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp (ht.1 hp)).1)
    have hcomp : (n.primeFactors \ t).prod id * t.prod id = n :=
      (Finset.prod_sdiff ht.1).trans hfull
    have hdvd : Dvd.dvd (t.prod id) n := by
      refine Exists.intro ((n.primeFactors \ t).prod id) ?_
      simpa only [Nat.mul_comm] using hcomp.symm
    refine Exists.intro (t.prod id) (And.intro hdvd (And.intro ?_ ?_))
    case refine_1 => simpa only [hfull] using ht.2.1
    case refine_2 => simpa only [hpf] using ht.2.2

end Nat
