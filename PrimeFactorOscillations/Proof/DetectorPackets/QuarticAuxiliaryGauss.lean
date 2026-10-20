/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.Linarith

/-!
# QuarticAuxiliaryGauss

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# The second Gauss coefficient in lower-order auxiliary probes

Quartic rows retain a nonprincipal quadratic second coefficient, of unit
normalized magnitude. For quadratic rows the second character is principal
and its Gauss coefficient has magnitude q^(-1/2). This prevents substituting
order two into an estimate that assumes the second normalized coefficient
has unit magnitude. It is not an obstruction to every quadratic approach.
-/


noncomputable section
namespace PrimeFactorOscillations.QuarticAuxiliaryGauss

def normalized {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (psi : AddChar F Complex) : Complex :=
  gaussSum chi psi / (Real.sqrt (Fintype.card F : Real) : Complex)

theorem square_character_at_neg_one {F : Type*} [Field F]
    (chi : MulChar F Complex) : (chi^2) (-1) = 1 := by
  calc
    _ = chi (-1)^2 := MulChar.pow_apply' chi (by decide) (-1)
    _ = chi ((-1 : F)^2) := (map_pow chi.toMonoidHom (-1) 2).symm
    _ = 1 := by simp

theorem quartic_second_gauss_square {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h4 : chi^4 = 1)
    (h2 : Not (chi^2 = 1)) (psi : AddChar F Complex) (hp : psi.IsPrimitive) :
    (gaussSum (chi^2) psi)^2 = (Fintype.card F : Complex) := by
  have hqq : (chi^2)*(chi^2) = 1 := by
    simpa only [<- pow_add] using h4
  have hinv : Inv.inv (chi^2) = chi^2 := by
    have hh := congrArg (fun x : MulChar F Complex => Inv.inv (chi^2)*x) hqq
    simpa only [<- mul_assoc, inv_mul_cancel, one_mul, mul_one] using hh.symm
  have hs := mul_gaussSum_inv_eq_gaussSum (chi^2) psi
  rw [square_character_at_neg_one chi, one_mul] at hs
  have hg := gaussSum_mul_gaussSum_eq_card h2 hp
  rw [hinv, hs] at hg
  simpa only [pow_two] using hg

theorem quartic_second_normalized_square {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h4 : chi^4 = 1)
    (h2 : Not (chi^2 = 1)) (psi : AddChar F Complex) (hp : psi.IsPrimitive) :
    (normalized (chi^2) psi)^2 = 1 := by
  have hq : Not ((Fintype.card F : Complex) = 0) :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F : Real) : Complex)^2 =
      (Fintype.card F : Complex) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F))
  rw [normalized, div_pow, quartic_second_gauss_square chi h4 h2 psi hp,
    hs, div_self hq]

theorem quartic_second_normalized_norm {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h4 : chi^4 = 1)
    (h2 : Not (chi^2 = 1)) (psi : AddChar F Complex) (hp : psi.IsPrimitive) :
    norm (normalized (chi^2) psi) = 1 := by
  have hh := congrArg norm (quartic_second_normalized_square chi h4 h2 psi hp)
  rw [norm_pow, norm_one] at hh
  nlinarith [norm_nonneg (normalized (chi^2) psi)]

theorem quadratic_second_normalized {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h2 : chi^2 = 1)
    (psi : AddChar F Complex) (hp : Not (psi = 1)) :
    normalized (chi^2) psi =
      -1 / (Real.sqrt (Fintype.card F : Real) : Complex) := by
  rw [h2, normalized, gaussSum_one_left hp]

theorem quadratic_second_normalized_norm {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h2 : chi^2 = 1)
    (psi : AddChar F Complex) (hp : Not (psi = 1)) :
    norm (normalized (chi^2) psi) =
      1 / Real.sqrt (Fintype.card F : Real) := by
  rw [quadratic_second_normalized chi h2 psi hp, norm_div, norm_neg, norm_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (Fintype.card F : Real))]

end PrimeFactorOscillations.QuarticAuxiliaryGauss
