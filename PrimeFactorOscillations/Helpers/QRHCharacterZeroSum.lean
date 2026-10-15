/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.WeightedZeroSum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# Power bounds for the retained Dirichlet zero sum

The exact BV zero indices and their multiplicities are retained. The audited
OAI seven-eighths input replaces the classical height-dependent zero-free gap.
The reciprocal-zero estimate is uniform in modulus, character and cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedCriticalZeroSum_le_seven_eighths_reciprocal
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hx : 1 <= x) (T : Real) (e : Option Complex) :
    norm (truncatedCriticalZeroSum chi x T e) <=
      (x : Real) ^ (7 / 8 : Real) *
        Finset.sum (retainedCriticalZeroIndices chi T e)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) := by
  have hxReal : (1 : Real) <= (x : Real) := by exact_mod_cast hx
  have hxPos : 0 < (x : Real) := zero_lt_one.trans_le hxReal
  have hTerm (p : SymmetricCompletedZeroIndex chi)
      (hp : Membership.mem (retainedCriticalZeroIndices chi T e) p) :
      norm ((x : Complex) ^ symmetricCompletedZeroValue p /
        symmetricCompletedZeroValue p) <=
        (x : Real) ^ (7 / 8 : Real) *
          norm ((1 : Complex) / symmetricCompletedZeroValue p) := by
    have hMem := (mem_retainedCriticalZeroIndices_iff
      (chi := chi) (T := T) (exceptional := e) (p := p)).mp hp
    have hZero : chi.LFunction (symmetricCompletedZeroValue p) = 0 := by
      simpa only [symmetricCompletedZeroValue] using
        LFunction_eq_zero_of_mem_criticalStripZeroTruncation hchi hPrimitive hMem.1
    have hRe : (symmetricCompletedZeroValue p).re <= (7 / 8 : Real) := by
      by_contra h
      exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
        chi (lt_of_not_ge h) (fun h => hchi h.1) hZero
    have hPower : norm ((x : Complex) ^ symmetricCompletedZeroValue p) <=
        (x : Real) ^ (7 / 8 : Real) := by
      rw [show (x : Complex) = ((x : Real) : Complex) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      exact Real.rpow_le_rpow_of_exponent_le hxReal hRe
    calc
      _ = norm ((x : Complex) ^ symmetricCompletedZeroValue p) *
          norm ((1 : Complex) / symmetricCompletedZeroValue p) := by
            rw [div_eq_mul_inv, norm_mul, one_div]
      _ <= _ := mul_le_mul_of_nonneg_right hPower (norm_nonneg _)
  rw [truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue]
  calc
    _ <= Finset.sum (retainedCriticalZeroIndices chi T e)
        (fun p => norm ((x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p)) := norm_sum_le _ _
    _ <= Finset.sum (retainedCriticalZeroIndices chi T e)
        (fun p => (x : Real) ^ (7 / 8 : Real) *
          norm ((1 : Complex) / symmetricCompletedZeroValue p)) :=
      Finset.sum_le_sum hTerm
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exists_norm_truncatedCriticalZeroSum_le_seven_eighths_log_sq
    {c : Real} (hc : 0 < c) :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Not (chi = 1) -> DirichletCharacter.IsPrimitive chi ->
          ExplicitFormulaZeroFreeData c chi ->
          forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
            forall {x : Nat}, 1 <= x -> forall {T : Real}, 0 < T ->
              norm (truncatedCriticalZeroSum chi x T e) <=
                K * (x : Real) ^ (7 / 8 : Real) *
                  (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) := by
  choose K hKPos hK using exists_sum_norm_one_div_retainedCriticalZeroIndices_le hc
  refine Exists.intro K (And.intro hKPos ?_)
  intro N inst hN chi hchi hPrimitive hData e hChoice x hx T hT
  have hDecay := norm_truncatedCriticalZeroSum_le_seven_eighths_reciprocal
    hchi hPrimitive hx T e
  have hReciprocal := hK hN hchi hPrimitive
    hData.regularGap hData.realUnique e hChoice T hT
  have hBound := hDecay.trans (mul_le_mul_of_nonneg_left hReciprocal
    (Real.rpow_nonneg (Nat.cast_nonneg x) _))
  calc
    _ <= (x : Real) ^ (7 / 8 : Real) *
        (K * (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) := hBound
    _ = _ := by ring

end PrimeFactorOscillations.QRH
