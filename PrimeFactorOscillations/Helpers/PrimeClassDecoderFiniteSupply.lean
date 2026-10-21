/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderFactorLower

/-!
# A uniform positive supply for the complete signed finite product

The existing class power sum controls the early cardinality and the late
reciprocal mass in the same exponent. The exact prime-label parity remains
on the complete finite Euler product.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

theorem halfInteger_finite_exponent_lower
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (R Y : Nat) (hR : 1 <= R)
    (hY : 4 * R + 2 <= Y) :
    -((6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma *
        Real.log (12 * (R : Real))) - 5 * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma <=
      (primeClassPrefix P Y).sum (fun p => if p <= 4 * R + 2 then
        -Real.log (12 * (R : Real)) else -5 * (R : Real) / (p : Real)) := by
  classical
  have hRpos : (0 : Real) < (R : Real) := by exact_mod_cast (by omega : 0 < R)
  have hRR : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have hlog : 0 <= Real.log (12 * (R : Real)) := Real.log_nonneg (by linarith)
  have hc := mul_le_mul_of_nonneg_right (earlyPrimeClass_card_le P sigma hs0 hsum R hR) hlog
  have ht := mul_le_mul_of_nonneg_left
    (latePrimeClass_reciprocal_mass_le P sigma hs1 hsum R Y hR)
    (by positivity : (0 : Real) <= 5 * R)
  have hRpower : (R : Real) * (R : Real) ^ (sigma - 1) = (R : Real) ^ sigma := by
    calc
      _ = (R : Real) ^ (1 : Real) * (R : Real) ^ (sigma - 1) := by rw [Real.rpow_one]
      _ = (R : Real) ^ (1 + (sigma - 1)) := (Real.rpow_add hRpos _ _).symm
      _ = _ := by congr 1; ring
  have hscale : 5 * (R : Real) *
      ((R : Real) ^ (sigma - 1) * tsum (classPowerWeight P sigma)) =
      5 * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma := by
    calc
      _ = 5 * tsum (classPowerWeight P sigma) *
          ((R : Real) * (R : Real) ^ (sigma - 1)) := by ring
      _ = _ := by rw [hRpower]
  rw [hscale] at ht
  rw [sum_halfInteger_lowerExponents, primeClassPrefix_filter_le P Y (4 * R + 2) hY]
  linarith

theorem finite_primeClass_halfInteger_signed_lower
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (R n Y : Nat)
    (hR : 1 <= R) (hn : n <= R) (hY : 4 * R + 2 <= Y) :
    Real.exp (-((6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma *
      Real.log (12 * (R : Real))) - 5 * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma) <=
        (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
          (primeClassPrefix P Y).prod
            (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
  classical
  have hpos : forall p : Nat, Membership.mem (primeClassPrefix P Y) p -> 0 < p := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2.1
    exact hpPrime.pos
  have hfinite := signed_halfInteger_prod_ge_exp_sum (primeClassPrefix P Y) R n hR hn hpos
  rw [primeClassPrefix_filter_le P Y (n + 1) (by omega)] at hfinite
  exact (Real.exp_le_exp.mpr (halfInteger_finite_exponent_lower P sigma hs0 hs1 hsum R Y hR hY))
    |>.trans hfinite

end PrimeFactorOscillations.PrimeClassSampling
