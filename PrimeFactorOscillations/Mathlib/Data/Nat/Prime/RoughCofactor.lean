/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Factors

/-!
# Prime cofactors above the cube-root least-factor threshold

A composite natural number below the cube of its least prime factor is a
product of two primes. The strict cube bound is essential; squares are allowed.
-/

namespace Nat

/-- A composite below the cube of its least prime factor has prime cofactor. -/
theorem prime_div_minFac_of_lt_cube (n : Nat) (hn : 1 < n)
    (hcomp : Not (Prime n)) (hcube : n < n.minFac ^ 3) :
    Prime (n / n.minFac) := by
  have hlp : Prime n.minFac := minFac_prime (by omega)
  have hla : n.minFac <= n / n.minFac := minFac_le_div (by omega) hcomp
  have ha : 1 < n / n.minFac := lt_of_lt_of_le hlp.one_lt hla
  have hprod : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' (minFac_dvd n)
  by_contra hnot
  have hqprime : Prime (n / n.minFac).minFac := minFac_prime (by omega)
  have hqdiv : Dvd.dvd ((n / n.minFac).minFac) n :=
    dvd_trans (minFac_dvd _) (Nat.div_dvd_of_dvd (minFac_dvd n))
  have hlq : n.minFac <= (n / n.minFac).minFac :=
    minFac_le_of_dvd hqprime.two_le hqdiv
  have hqsq : (n / n.minFac).minFac ^ 2 <= n / n.minFac :=
    minFac_sq_le_self (by omega) hnot
  have hlsq : n.minFac ^ 2 <= n / n.minFac :=
    le_trans (Nat.pow_le_pow_left hlq 2) hqsq
  have hle : n.minFac ^ 3 <= n := calc
    n.minFac ^ 3 = n.minFac * (n.minFac ^ 2) := by rw [pow_succ, Nat.mul_comm]
    _ <= n.minFac * (n / n.minFac) := Nat.mul_le_mul_left _ hlsq
    _ = n := hprod
  exact (Nat.not_lt_of_ge hle) hcube

end Nat
