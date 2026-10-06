/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileGenerating
import PrimeFactorOscillations.Helpers.QuadraticProfileRootShift

/-!
# Generalized reference-scale constants

The local level 1 + g/nu gives leading scale rank/(g+nu). The correction is
the logarithmic derivative of the full family profile divided by nu. This
is the reference crossing; identifying an actual last ascent needs the
separate arithmetic occurrence and local-threshold precision hypotheses.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

noncomputable def referenceScaleConstant (law : QuadraticPrimeLaw) (g : Real) : Real :=
  Real.eulerMascheroniConstant +
    (deriv (fun t : Real => (law.complexProfile (t : Complex)).re) (1 + g / law.nu) /
      (law.complexProfile ((1 + g / law.nu : Real) : Complex)).re) / law.nu

theorem exists_reference_scale_with_sharp_constant (law : QuadraticPrimeLaw)
    (g : Real) (hg : 0 <= g) :
    exists C : Real, exists r0 : Nat, 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> exists u T : Real,
        T = Real.exp (Real.exp (u / law.nu - Real.eulerMascheroniConstant)) /\
        Nat.factorialConvolution law.realCoefficient (r - 1) u /
          Nat.factorialConvolution law.realCoefficient r u = 1 + g / law.nu /\
        abs (Real.log (Real.log T) -
          ((r : Real) / (g + law.nu) - law.referenceScaleConstant g)) <= C / r := by
  have hs : 0 < 1 + g / law.nu := by have hNu := law.nu_pos; positivity
  choose A C r0 hA hC hr0 hRoot using law.exists_profile_reference_sharp_crossing
    (1 + g / law.nu) hs
  refine Exists.intro (C / law.nu) (Exists.intro r0
    (And.intro (div_nonneg hC law.nu_pos.le) (And.intro hr0 ?_)))
  intro r hr
  choose u hu hEq hError hUnique using hRoot r hr
  let T := Real.exp (Real.exp (u / law.nu - Real.eulerMascheroniConstant))
  refine Exists.intro u (Exists.intro T (And.intro rfl (And.intro hEq ?_)))
  have hDen : 0 < g + law.nu := by have hNu := law.nu_pos; linarith
  have hScale : (r : Real) / (g + law.nu) = ((r : Real) / (1 + g / law.nu)) / law.nu := by
    rw [div_div]
    congr 1
    field_simp [law.nu_pos.ne']
    <;> ring
  have hId : Real.log (Real.log T) -
      ((r : Real) / (g + law.nu) - law.referenceScaleConstant g) =
      (u - (r : Real) / (1 + g / law.nu) +
        deriv (fun t : Real => (law.complexProfile (t : Complex)).re) (1 + g / law.nu) /
          (law.complexProfile ((1 + g / law.nu : Real) : Complex)).re) / law.nu := by
    dsimp [T, referenceScaleConstant]
    rw [Real.log_exp, Real.log_exp, hScale]
    ring
  rw [hId, abs_div, abs_of_pos law.nu_pos]
  calc
    _ <= (C / (r : Real)) / law.nu := div_le_div_of_nonneg_right hError law.nu_pos.le
    _ = (C / law.nu) / r := by ring

end PrimeFactorOscillations.QuadraticPrimeLaw
