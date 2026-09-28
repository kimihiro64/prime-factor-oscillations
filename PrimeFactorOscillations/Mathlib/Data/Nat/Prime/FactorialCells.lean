/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.CompositeBlocks

/-! # Prime locations between periodic factorial barriers -/

namespace Nat

/-- A prime lies after the composite prefix of its factorial cell. -/
theorem prime_factorial_cell_bounds {L p : Nat} (hp : Nat.Prime p)
    (hlarge : Nat.factorial L + 2 <= p) :
    let c := (p - 2) / Nat.factorial L
    0 < c /\ c * Nat.factorial L + L + 1 <= p /\
      p <= (c + 1) * Nat.factorial L + 1 := by
  dsimp only
  let F := Nat.factorial L
  let c := (p - 2) / F
  have hF : 0 < F := Nat.factorial_pos L
  have hp2 : 2 <= p := hp.two_le
  have hmod : (p - 2) % F < F := Nat.mod_lt _ hF
  have hdecomp : (p - 2) % F + c * F = p - 2 := by
    simpa only [c, Nat.mul_comm] using Nat.mod_add_div (p - 2) F
  have hc : 0 < c := by
    change F + 2 <= p at hlarge
    by_contra hn
    have hz : c = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, Nat.zero_mul] at hdecomp
    omega
  have hlo : c * F + 2 <= p := by omega
  have hhi : p <= (c + 1) * F + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hafter : c * F + L + 1 <= p := by
    by_contra hn
    have hj : 2 <= p - c * F := by omega
    have hjL : p - c * F <= L := by omega
    have hnot := Nat.not_prime_mul_factorial_add (L := L) hc hj hjL
    have heq : c * Nat.factorial L + (p - c * F) = p := by
      change c * F + (p - c * F) = p
      omega
    rw [heq] at hnot
    exact hnot hp
  exact And.intro hc (And.intro hafter hhi)

/-- Two nearby primes cannot cross the next factorial composite block. -/
theorem short_prime_pair_same_factorial_cell {L H p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hlarge : Nat.factorial L + 2 <= p)
    (hshort : q <= p + H) (hHL : H + 1 <= L) :
    q <= ((p - 2) / Nat.factorial L + 1) * Nat.factorial L + 1 := by
  let c := (p - 2) / Nat.factorial L
  have hb := prime_factorial_cell_bounds hp hlarge
  change 0 < c /\ c * Nat.factorial L + L + 1 <= p /\
    p <= (c + 1) * Nat.factorial L + 1 at hb
  change q <= (c + 1) * Nat.factorial L + 1
  by_contra hn
  have hj : 2 <= q - (c + 1) * Nat.factorial L := by omega
  have hjL : q - (c + 1) * Nat.factorial L <= L := by omega
  have hnot := Nat.not_prime_mul_factorial_add (L := L)
    (Nat.succ_pos c) hj hjL
  have heq : (c + 1) * Nat.factorial L +
      (q - (c + 1) * Nat.factorial L) = q := by omega
  rw [heq] at hnot
  exact hnot hq

end Nat
