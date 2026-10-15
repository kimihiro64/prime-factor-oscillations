/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrincipalCharacter

/-!
# Centered uniform character-prefix source

The principal and nonprincipal cases share one constant before the modulus.
The exact finite Euler correction remains in the principal estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz Robin1984

noncomputable def lpfCharacterPrefixCenter {N : Nat}
    (chi : DirichletCharacter Complex N) : Complex := by
  classical
  exact if chi = 1 then 1 else 0

/-- One constant works before every modulus, character and sufficiently large prefix. -/
theorem exists_all_characterChebyshevSum_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        forall {x : Nat}, 65536 <= x ->
          norm (characterChebyshevSum x chi - (x : Complex) * lpfCharacterPrefixCenter chi) <=
            A * (x : Real) ^ (15 / 16 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  classical
  let A0 : Real := Classical.choose exists_characterChebyshevSum_le_seven_eighths
  have hA0All := Classical.choose_spec exists_characterChebyshevSum_le_seven_eighths
  have hA0 : 0 < A0 := hA0All.1
  have hC := lpfPrincipalPointwiseConstant_pos
  have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  refine Exists.intro (A0 + lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real))
    (And.intro (by positivity) ?_)
  intro N inst chi x hx
  have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast (by omega : 1 <= x)
  have hPow := Real.rpow_nonneg (zero_le_one.trans hxR) (15 / 16 : Real)
  let B : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hFactor : 0 <= (x : Real) ^ (15 / 16 : Real) * B ^ 2 :=
    mul_nonneg hPow (sq_nonneg B)
  by_cases hChi : chi = 1
  . subst chi
    simp [lpfCharacterPrefixCenter]
    have h := norm_principal_characterChebyshevSum_sub_nat_le (N := N) hx
    have hCoeff : lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real) <=
        A0 + lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real) := by
      linarith only [hA0]
    have hMul := mul_le_mul_of_nonneg_right hCoeff hFactor
    have hEnd := h.trans (by simpa only [B, mul_assoc] using hMul)
    simpa only [B, mul_assoc, one_div] using hEnd
  . simp only [lpfCharacterPrefixCenter, ite_eq_right hChi, mul_zero, sub_zero]
    have h := hA0All.2 chi hChi (by omega : 2 <= x)
    have hPower : (x : Real) ^ (7 / 8 : Real) <= (x : Real) ^ (15 / 16 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hxR (by norm_num)
    have hRelax := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPower hA0.le) (sq_nonneg B)
    have hCoeff : A0 <= A0 + lpfPrincipalPointwiseConstant + 1 / Real.log (2 : Real) := by
      have hInv : 0 <= 1 / Real.log (2 : Real) := by positivity
      linarith only [hC, hInv]
    have hMul := mul_le_mul_of_nonneg_right hCoeff hFactor
    exact (h.trans hRelax).trans (by simpa only [B, mul_assoc] using hMul)

end PrimeFactorOscillations.QRH
