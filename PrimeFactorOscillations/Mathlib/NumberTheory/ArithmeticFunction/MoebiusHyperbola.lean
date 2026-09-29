/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option autoImplicit false


/-!
# Mobius sums below the divisor hyperbola

For an integer greater than one with Mobius value one, complementary divisors
have equal Mobius values. Their total is zero, and so is the sum on either
side of the divisor hyperbola. The inclusive square-root cutoff is represented
exactly by the predicate d * d <= n.

These finite identities provide no estimate on shifted prime averages.
-/

namespace ArithmeticFunction

/-- Complementary divisors have equal Mobius values when the product has value one. -/
theorem moebius_div_eq_of_eq_one (n d : Nat) (hn : moebius n = 1)
    (hd : Dvd.dvd d n) : moebius (n / d) = moebius d := by
  have hsf : Squarefree n := moebius_ne_zero_iff_squarefree.mp (by rw [hn]; decide)
  have hcop : Nat.Coprime d (n / d) :=
    Nat.coprime_of_squarefree_mul (by simpa only [Nat.mul_div_cancel' hd] using hsf)
  have hprod : moebius d * moebius (n / d) = 1 := by
    rw [<- isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.mul_div_cancel' hd, hn]
  rcases moebius_eq_or d with h0 | h1 | hneg
  case inl => simp [h0] at hprod
  case inr.inl => simpa [h1] using hprod
  case inr.inr =>
    rw [hneg] at hprod
    rw [hneg]
    omega

/-- Pairing complementary divisors makes the lower hyperbola sum vanish. -/
theorem sum_moebius_divisors_le_div_eq_zero (n : Nat) (hn : 1 < n)
    (hmu : moebius n = 1) :
    Finset.sum (n.divisors.filter (fun d => d <= n / d)) (fun d => moebius d) = 0 := by
  have hn0 : Not (n = 0) := by omega
  have hn1 : Not (n = 1) := by omega
  have hsf : Squarefree n := moebius_ne_zero_iff_squarefree.mp (by rw [hmu]; decide)
  let f : Nat -> Int := fun d => if d <= n / d then moebius d else 0
  have hpoint : forall d, Membership.mem n.divisors d ->
      f d + f (n / d) = moebius d := by
    intro d hmem
    have hd := (Nat.mem_divisors.mp hmem).1
    have hcop : Nat.Coprime d (n / d) :=
      Nat.coprime_of_squarefree_mul (by simpa only [Nat.mul_div_cancel' hd] using hsf)
    have hne : Not (d = n / d) := by
      intro heq
      rw [<- heq] at hcop
      have hd1 : d = 1 := by simpa only [Nat.coprime_self] using hcop
      exact hn1 (by simpa only [hd1, Nat.div_one] using heq.symm)
    have hinv : n / (n / d) = d := Nat.div_div_self hd hn0
    have hval := moebius_div_eq_of_eq_one n d hmu hd
    by_cases hle : d <= n / d
    case pos =>
      have hnot : Not (n / d <= d) := by omega
      simp only [f, hinv, hle, hnot, ite_true, ite_false, add_zero]
    case neg =>
      have hrev : n / d <= d := by omega
      simp only [f, hinv, hle, hrev, ite_true, ite_false, zero_add, hval]
  have htotal : Finset.sum n.divisors (fun d => moebius d) = 0 := by
    rw [<- coe_mul_zeta_apply, moebius_mul_coe_zeta]
    simp [hn1]
  have hsum : Finset.sum n.divisors f + Finset.sum n.divisors f = 0 := by
    calc
      Finset.sum n.divisors f + Finset.sum n.divisors f =
          Finset.sum n.divisors (fun d => f d + f (n / d)) := by
            rw [Finset.sum_add_distrib, Nat.sum_div_divisors]
      _ = Finset.sum n.divisors (fun d => moebius d) := Finset.sum_congr rfl hpoint
      _ = 0 := htotal
  have hzero : Finset.sum n.divisors f = 0 := by omega
  simpa only [Finset.sum_filter, f] using hzero

/-- The lower half of the divisor sum vanishes when the Mobius value is one. -/
theorem sum_moebius_divisors_mul_self_le_eq_zero (n : Nat) (hn : 1 < n)
    (hmu : moebius n = 1) :
    Finset.sum (n.divisors.filter (fun d => d * d <= n)) (fun d => moebius d) = 0 := by
  have hfilter : n.divisors.filter (fun d => d * d <= n) =
      n.divisors.filter (fun d => d <= n / d) := by
    apply Finset.filter_congr
    intro d hd
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)).symm
  rw [hfilter]
  exact sum_moebius_divisors_le_div_eq_zero n hn hmu

end ArithmeticFunction
