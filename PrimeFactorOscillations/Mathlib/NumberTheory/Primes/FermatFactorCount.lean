/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FermatCarrier

/-!
# Uniform bounds for all prime factors of Fermat numbers

The exact order theorem bounds every prime factor from below. Their
distinct product divides the Fermat number, giving an integer bound on
the full factor count. These weights feed the complete nested-clock
distribution, rather than an independent model for individual factors.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- Every physical prime factor is strictly larger than its dyadic order. -/
theorem prime_factor_fermat_lower_bound (j r : Nat) (hr : Prime r)
    (hd : Dvd.dvd r (2 ^ (2 ^ j) + 1)) : 2 ^ (j + 1) + 1 <= r := by
  let _ : NeZero r := NeZero.mk hr.ne_zero
  have ht : 2 < r := prime_factor_fermat_two_lt j r hr hd
  have ho : 2 ^ (j + 1) <= r := by
    have h := orderOf_le_card_univ (x := (2 : ZMod r))
    rw [fermat_divisor_order j r ht hd, ZMod.card] at h
    exact h
  have hn : Not (r = 2 ^ (j + 1)) := by
    intro he
    have hd2 : Dvd.dvd r 2 := hr.dvd_of_dvd_pow (by rw [he])
    exact (not_le_of_gt ht) (Nat.le_of_dvd (by decide : 0 < 2) hd2)
  exact Nat.succ_le_iff.mpr (_root_.lt_of_le_of_ne ho (Ne.symm hn))

/-- The number of distinct physical prime factors at one Fermat label. -/
def fermatFactorCount (j : Nat) : Nat :=
  (2 ^ (2 ^ j) + 1).primeFactors.card

theorem fermatFactorCount_pos (j : Nat) : 0 < fermatFactorCount j := by
  apply Finset.card_pos.mpr
  exact Exists.intro (fermatPrimeCarrier j)
    (mem_primeFactors.mpr (And.intro (fermatPrimeCarrier_prime j)
      (And.intro (fermatPrimeCarrier_dvd j) (Nat.succ_ne_zero _))))

/-- A uniform all-label bound, including the first Fermat number. -/
theorem fermatFactorCount_mul_le_pow (j : Nat) :
    (j + 1) * fermatFactorCount j <= 2 ^ j := by
  let S := (2 ^ (2 ^ j) + 1).primeFactors
  have hprod : (2 ^ (j + 1) + 1) ^ S.card <= S.prod (fun r => r) := by
    rw [<- Finset.prod_const]
    apply Finset.prod_le_prod
    intro r hr
    have hp := mem_primeFactors.mp hr
    exact prime_factor_fermat_lower_bound j r hp.1 hp.2.1
  have hupper : S.prod (fun r => r) <= 2 ^ (2 ^ j) + 1 :=
    Nat.le_of_dvd (Nat.succ_pos _) (prod_primeFactors_dvd _)
  have hpos : Not (S.card = 0) := Nat.ne_of_gt (fermatFactorCount_pos j)
  have hstrict : (2 ^ (j + 1)) ^ S.card < 2 ^ (2 ^ j) + 1 :=
    _root_.lt_of_lt_of_le (Nat.pow_lt_pow_left (Nat.lt_succ_self _) hpos)
      (hprod.trans hupper)
  rw [<- pow_mul] at hstrict
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.lt_succ_iff.mp hstrict)

/-- Different Fermat labels have disjoint full prime-factor supports. -/
theorem fermat_primeFactors_disjoint (i j : Nat) (hne : Not (i = j)) :
    Disjoint (2 ^ (2 ^ i) + 1).primeFactors (2 ^ (2 ^ j) + 1).primeFactors := by
  apply Finset.disjoint_left.mpr
  intro r hi hj
  have hpi := mem_primeFactors.mp hi
  have hpj := mem_primeFactors.mp hj
  have ht : 2 < r := prime_factor_fermat_two_lt i r hpi.1 hpi.2.1
  have he : 2 ^ (i + 1) = 2 ^ (j + 1) :=
    (fermat_divisor_order i r ht hpi.2.1).symm.trans
      (fermat_divisor_order j r ht hpj.2.1)
  apply hne
  exact Nat.add_right_cancel (Nat.pow_right_injective (by decide : 2 <= 2) he)

end Nat
