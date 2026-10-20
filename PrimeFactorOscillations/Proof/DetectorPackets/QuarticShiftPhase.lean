/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.GaussSum

/-!
# QuarticShiftPhase

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
# Exact square and cube twists of quartic Gauss sums

The square shift retains a quadratic character. The cube shift retains the
original quartic character. These identities keep the phase of the
unramified reflected coefficient; they do not identify the two row families.
The unit hypotheses do not cover common-prime layers, which require a
separate prime-power and CRT computation.
-/


noncomputable section
namespace PrimeFactorOscillations.QuarticShiftPhase

variable {F : Type} [Field F] [Fintype F]

theorem inverse_square (chi : MulChar F Complex) (h4 : chi^4 = 1) :
    (Inv.inv chi)^2 = chi^2 := by
  have hqq : chi^2 * chi^2 = 1 := by
    simpa only [<- pow_add] using h4
  have hinv : Inv.inv (chi^2) = chi^2 := by
    have hh := congrArg (fun x : MulChar F Complex => Inv.inv (chi^2) * x) hqq
    simpa only [<- mul_assoc, inv_mul_cancel, one_mul, mul_one] using hh.symm
  rw [inv_pow]
  exact hinv

theorem inverse_cube (chi : MulChar F Complex) (h4 : chi^4 = 1) :
    (Inv.inv chi)^3 = chi := by
  have hqq : chi^3 * chi = 1 := by
    simpa only [<- pow_succ] using h4
  have hinv : Inv.inv (chi^3) = chi := by
    have hh := congrArg (fun x : MulChar F Complex => Inv.inv (chi^3) * x) hqq
    simpa only [<- mul_assoc, inv_mul_cancel, one_mul, mul_one] using hh.symm
  rw [inv_pow]
  exact hinv

theorem square_shift (chi : MulChar F Complex) (h4 : chi^4 = 1)
    (psi : AddChar F Complex) (u : Units F) :
    gaussSum chi (psi.mulShift ((u^2 : Units F) : F)) =
      (chi^2) (u : F) * gaussSum chi psi := by
  rw [gaussSum_mulShift_eq]
  have hchar : Inv.inv chi ((u^2 : Units F) : F) = (chi^2) (u : F) := by
    calc
      _ = (Inv.inv chi (u : F))^2 := by
        change Inv.inv chi ((u : F)^2) = (Inv.inv chi (u : F))^2
        exact map_pow (Inv.inv chi).toMonoidHom (u : F) 2
      _ = ((Inv.inv chi)^2) (u : F) := by
        rw [MulChar.pow_apply' (Inv.inv chi) (by decide : Not (2 = 0))]
      _ = _ := by rw [inverse_square chi h4]
  rw [hchar]

theorem cube_shift (chi : MulChar F Complex) (h4 : chi^4 = 1)
    (psi : AddChar F Complex) (u : Units F) :
    gaussSum chi (psi.mulShift ((u^3 : Units F) : F)) =
      chi (u : F) * gaussSum chi psi := by
  rw [gaussSum_mulShift_eq]
  have hchar : Inv.inv chi ((u^3 : Units F) : F) = chi (u : F) := by
    calc
      _ = (Inv.inv chi (u : F))^3 := by
        change Inv.inv chi ((u : F)^3) = (Inv.inv chi (u : F))^3
        exact map_pow (Inv.inv chi).toMonoidHom (u : F) 3
      _ = ((Inv.inv chi)^3) (u : F) := by
        rw [MulChar.pow_apply' (Inv.inv chi) (by decide : Not (3 = 0))]
      _ = _ := by rw [inverse_cube chi h4]
  rw [hchar]

end PrimeFactorOscillations.QuarticShiftPhase
