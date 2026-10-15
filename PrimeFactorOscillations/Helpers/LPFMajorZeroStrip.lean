/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.QRHCharacterZeroSum

/-!
# Fixed numerical separation of primitive Dirichlet zeros

Reflection transfers the audited seven-eighths nonvanishing theorem to a
one-eighth lower bound on the real part. In particular every reciprocal
critical zero has norm at most eight, independent of the classical
Siegel-Walfisz zero-free constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_gammaFactor_ne_zero_of_pos_re
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex)
    (hs : 0 < s.re) : Not (chi.gammaFactor s = 0) := by
  unfold DirichletCharacter.gammaFactor
  split_ifs
  next =>
    change Not ((((Real.pi : Complex) ^ (-s / 2)) * Complex.Gamma (s / 2)) = 0)
    apply mul_ne_zero
    next => exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
    next =>
      apply Complex.Gamma_ne_zero
      intro m h
      have hh := congrArg Complex.re h
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.natCast_re] at hh
      have hm : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
      norm_num at hh
      linarith only [hh, hs, hm]
  next =>
    change Not ((((Real.pi : Complex) ^ (-(s + 1) / 2)) * Complex.Gamma ((s + 1) / 2)) = 0)
    apply mul_ne_zero
    next => exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
    next =>
      apply Complex.Gamma_ne_zero
      intro m h
      have hh := congrArg Complex.re h
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.natCast_re,
        Complex.add_re] at hh
      have hm : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
      norm_num at hh
      linarith only [hh, hs, hm]

theorem lpf_critical_zero_re_lower_one_eighth
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (rho : Complex) (hPos : 0 < rho.re) (hZero : chi.LFunction rho = 0) :
    (1 / 8 : Real) <= rho.re := by
  by_contra h
  have hRight : (7 / 8 : Real) < (1 - rho).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [lt_of_not_ge h]
  have hInvPrimitive : DirichletCharacter.IsPrimitive (Inv.inv chi) := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hPrimitive
  have hRho : Not (rho = 0) := by
    intro he
    rw [he, Complex.zero_re] at hPos
    exact lt_irrefl 0 hPos
  have hGamma := lpf_gammaFactor_ne_zero_of_pos_re chi rho hPos
  have hCompleted : chi.completedLFunction rho = 0 := by
    have he := (div_eq_iff hGamma).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi rho (Or.inl hRho)).symm
    rw [hZero, zero_mul] at he
    exact he
  have hInvCompleted : (Inv.inv chi).completedLFunction (1 - rho) = 0 := by
    have he := hInvPrimitive.completedLFunction_one_sub rho
    simpa only [inv_inv, hCompleted, mul_zero] using he
  have hOneSub : Not (1 - rho = 0) := by
    intro he
    rw [he, Complex.zero_re] at hRight
    norm_num at hRight
  have hInvZero : (Inv.inv chi).LFunction (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      (Inv.inv chi) (1 - rho) (Or.inl hOneSub), hInvCompleted, zero_div]
  have hInvNot : Not (Inv.inv chi = 1) := by
    intro he
    apply hchi
    have hi := congrArg Inv.inv he
    simpa only [inv_inv, inv_one] using hi
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    (Inv.inv chi) hRight (fun he => hInvNot he.1) hInvZero

theorem lpf_critical_zero_reciprocal_norm_le_eight
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (rho : Complex) (hPos : 0 < rho.re) (hZero : chi.LFunction rho = 0) :
    norm ((1 : Complex) / rho) <= 8 := by
  have hRe := lpf_critical_zero_re_lower_one_eighth chi hchi hPrimitive rho hPos hZero
  have hNorm : (1 / 8 : Real) <= norm rho := hRe.trans (Complex.re_le_norm rho)
  rw [norm_div, norm_one]
  calc
    _ <= 1 / (1 / 8 : Real) := one_div_le_one_div_of_le (by norm_num) hNorm
    _ = _ := by norm_num

end PrimeFactorOscillations.QRH
