/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticPrimeCriterion
import PrimeFactorOscillations.Helpers.ReciprocalSmoothOdds

/-!
# Every reciprocal-smooth local law qualifies for the RH product criterion

The construction uses the previously proved global odds error, including all
finite exceptions. At forced primes eta = 1 the field odds are zero. This is
the generating product after removing those deterministic coordinates; their
number must still be subtracted from the rank in density applications.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem quadraticPrimeWeight_error_of_inverse_prime
    (w : Nat.Primes -> Real) (nu D : Real) (hnu : 0 <= nu) (hD : 0 <= D)
    (hError : forall p : Nat.Primes, abs (w p - nu / (p : Real)) <= D / (p : Real) ^ 2)
    (p : Nat.Primes) :
    abs (w p - nu * primeProfileWeight (p : Nat)) <=
      (D + nu) * (primeProfileWeight (p : Nat)) ^ 2 := by
  let v := primeProfileWeight (p : Nat)
  let t : Real := 1 / (p : Real)
  have hp : (0 : Real) < p := by exact_mod_cast p.property.pos
  have hpOne : (0 : Real) < (((p : Nat) - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < (p : Nat) - 1 by have h := p.property.two_le; omega)
  have ht : 0 <= t := by dsimp [t]; positivity
  have hv : 0 <= v := primeProfileWeight_nonneg _
  have htv : t <= v := by
    dsimp [t, v, primeProfileWeight]
    exact one_div_le_one_div_of_le hpOne (by exact_mod_cast Nat.sub_le (p : Nat) 1)
  have hDifference : v - t = v * t := by
    have hCast : (((p : Nat) - 1 : Nat) : Real) = (p : Real) - 1 := by
      rw [Nat.cast_sub p.property.one_lt.le, Nat.cast_one]
    have hpGt : (1 : Real) < (p : Real) := by exact_mod_cast p.property.one_lt
    have hPos : 0 < (p : Real) - 1 := by linarith only [hpGt]
    dsimp [v, t, primeProfileWeight]
    rw [hCast]
    field_simp [hp.ne', hPos.ne']
    <;> ring
  have hDifferenceBound : v - t <= v ^ 2 := by
    rw [hDifference]
    nlinarith only [mul_le_mul_of_nonneg_left htv hv]
  have hBase : abs (w p - nu * t) <= D * v ^ 2 := by
    have h := hError p
    have hSquare : t ^ 2 <= v ^ 2 := by gcongr
    have hDScale := mul_le_mul_of_nonneg_left hSquare hD
    have hEq : D / (p : Real) ^ 2 = D * t ^ 2 := by dsimp [t]; ring
    have hNuEq : nu / (p : Real) = nu * t := by dsimp [t]; ring
    rw [hEq, hNuEq] at h
    exact h.trans hDScale
  have hShift : abs (nu * t - nu * v) <= nu * v ^ 2 := by
    have hsign : nu * t - nu * v <= 0 := by nlinarith only [mul_le_mul_of_nonneg_left htv hnu]
    rw [abs_of_nonpos hsign]
    nlinarith only [mul_le_mul_of_nonneg_left hDifferenceBound hnu]
  change abs (w p - nu * v) <= (D + nu) * v ^ 2
  calc
    _ = abs ((w p - nu * t) + (nu * t - nu * v)) := by congr 1; ring
    _ <= abs (w p - nu * t) + abs (nu * t - nu * v) := abs_add_le _ _
    _ <= D * v ^ 2 + nu * v ^ 2 := add_le_add hBase hShift
    _ = _ := by ring

namespace ReciprocalSmoothLaw

noncomputable def quadraticPrimeLaw (law : ReciprocalSmoothLaw) : QuadraticPrimeLaw := by
  let D := Classical.choose law.odds_global_error
  have hD := Classical.choose_spec law.odds_global_error
  refine {
    weight := fun p => law.eta (p : Nat) / (1 - law.eta (p : Nat))
    nu := law.nu
    error := D + law.nu
    nu_pos := law.nu_pos
    error_nonneg := add_nonneg hD.1.le law.nu_pos.le
    weight_nonneg := ?_
    quadratic_error := ?_
  }
  . intro p
    exact div_nonneg (law.probability (p : Nat) p.property).1
      (sub_nonneg.mpr (law.probability (p : Nat) p.property).2)
  . exact quadraticPrimeWeight_error_of_inverse_prime
      (fun p : Nat.Primes => law.eta (p : Nat) / (1 - law.eta (p : Nat)))
      law.nu D law.nu_pos.le hD.1.le (fun p => hD.2 (p : Nat) p.property)

@[simp] theorem quadraticPrimeLaw_nu (law : ReciprocalSmoothLaw) :
    law.quadraticPrimeLaw.nu = law.nu := rfl

@[simp] theorem quadraticPrimeLaw_weight (law : ReciprocalSmoothLaw) (p : Nat.Primes) :
    law.quadraticPrimeLaw.weight p = law.eta (p : Nat) / (1 - law.eta (p : Nat)) := rfl

theorem riemannHypothesis_iff_eventually_prime_product
    (law : ReciprocalSmoothLaw) (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      law.quadraticPrimeLaw.referenceConstant z *
        (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) <
      (primeProfilePrefixSet N).prod (fun p =>
        1 + law.eta (p : Nat) / (1 - law.eta (p : Nat)) * z)) Filter.atTop := by
  exact law.quadraticPrimeLaw.riemannHypothesis_iff_eventually_product z hz

end ReciprocalSmoothLaw

end PrimeFactorOscillations
