/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileClockLimit

/-!
# Exact finite prime-product clock identity

Relates the logarithm of a finite Nicolas-type product to the difference
between its reference clock and the inclusive prime-prefix clock.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primePrefixProfile_logProduct_eq_clock_difference
    (N : Nat) (gamma y : Real) (hy : 1 < y) :
    Real.log (Real.exp gamma * Real.log y *
      ((Finset.Ioc 0 N).filter Nat.Prime).prod (fun p => 1 - 1 / (p : Real))) =
      gamma + Real.log (Real.log y) -
        (primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat))) := by
  have hfactor : forall p, Membership.mem ((Finset.Ioc 0 N).filter Nat.Prime) p ->
      0 < 1 - 1 / (p : Real) := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpR : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hpPos : (0 : Real) < p := by linarith
    exact sub_pos.mpr ((div_lt_one hpPos).mpr hpR)
  have hprod : 0 < ((Finset.Ioc 0 N).filter Nat.Prime).prod
      (fun p => 1 - 1 / (p : Real)) := Finset.prod_pos hfactor
  have hlog : 0 < Real.log y := Real.log_pos hy
  rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos gamma) hlog)) (ne_of_gt hprod),
    Real.log_mul (ne_of_gt (Real.exp_pos gamma)) (ne_of_gt hlog), Real.log_exp,
    Real.log_prod (fun p hp => ne_of_gt (hfactor p hp)),
    primePrefixProfile_logSum_eq_neg_logProduct]
  ring

end PrimeFactorOscillations
