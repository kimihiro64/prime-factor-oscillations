/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# Bounding the explicitly retained exceptional contribution

The source zero-free data puts its selected exceptional zero to the right of
3/4, and the audited QRH theorem puts every nonprincipal zero at or left of
7/8. Hence even the exceptional term obeys the same power bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz

theorem norm_exceptionalZeroContribution_le_seven_eighths
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {c : Real}
    (hData : ExplicitFormulaZeroFreeData c chi)
    (e : Option Complex) (hChoice : IsExceptionalZeroChoice c chi e)
    (hx : 1 <= x) :
    norm (exceptionalZeroContribution x e) <= 2 * (x : Real) ^ (7 / 8 : Real) := by
  have hxReal : (1 : Real) <= (x : Real) := by exact_mod_cast hx
  have hxPos : 0 < (x : Real) := zero_lt_one.trans_le hxReal
  cases e with
  | none =>
    change norm (0 : Complex) <= _
    rw [norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hxPos.le _)
  | some beta =>
    have hExceptional : IsExceptionalZero c chi beta := hChoice
    have hFacts := hData.exceptional beta hExceptional
    have hRe : beta.re <= (7 / 8 : Real) := by
      by_contra h
      exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
        chi (lt_of_not_ge h) (fun h => hchi h.1) hExceptional.1
    have hNorm : (1 / 2 : Real) <= norm beta := by
      have h := Complex.re_le_norm beta
      linarith [hFacts.re_lower]
    have hInv : norm ((1 : Complex) / beta) <= 2 := by
      rw [norm_div, norm_one]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 2) hNorm
      norm_num at h
      simpa only [one_div] using h
    have hPower : norm ((x : Complex) ^ beta) <= (x : Real) ^ (7 / 8 : Real) := by
      rw [show (x : Complex) = ((x : Real) : Complex) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      exact Real.rpow_le_rpow_of_exponent_le hxReal hRe
    change norm ((x : Complex) ^ beta / beta) <= _
    calc
      _ = norm ((x : Complex) ^ beta) * norm ((1 : Complex) / beta) := by
        rw [div_eq_mul_inv, norm_mul, one_div]
      _ <= (x : Real) ^ (7 / 8 : Real) * 2 :=
        mul_le_mul hPower hInv (norm_nonneg _) (Real.rpow_nonneg hxPos.le _)
      _ = _ := mul_comm _ _

end PrimeFactorOscillations.QRH
