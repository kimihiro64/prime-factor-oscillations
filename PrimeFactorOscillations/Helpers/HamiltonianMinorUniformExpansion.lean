/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorUniformError

/-! # The full uniform two-power minor expansion

One threshold covers all finite coordinate types, every admissible
kernel, entry cap and pair of independent deleted supports.
No repair or local analytic estimate remains as a hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u

theorem stochastic_minor_two_power_polylog_uniform (delta K : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    0 < hamiltonianMinorUniformConstant delta /\
    exists N0 : Nat, 32 <= N0 /\
      forall (Iota : Type u) [Fintype Iota] [DecidableEq Iota] [Nonempty Iota],
        N0 <= Fintype.card Iota ->
        forall (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
          (q a : Real),
          (Fintype.card Iota : Real) * q = 1 -> 1 <= a ->
          a <= (Real.log (Fintype.card Iota : Real)) ^ K ->
          (U.card : Real) <= (Real.log (2 * (Fintype.card Iota : Real))) ^ 3 ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
          abs ((rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
            weightedPermutationSum T) ^ 2 - (1 + hamiltonianMinorFirstOrder T S U q)) <=
              hamiltonianMinorUniformConstant delta *
                (Real.log (2 * (Fintype.card Iota : Real))) ^ hamiltonianMinorUniformExponent K /
                  (Fintype.card Iota : Real) ^ 2 := by
  let common := stochastic_minor_permanent_common_uniform_range.{u} delta K hDelta hDelta1 hK
  let scalar := hamiltonian_minor_polylog_uniform_range delta K 0 hDelta hDelta1 hK
  let errors := hamiltonian_minor_uniform_error_range delta K hDelta hDelta1 hK
  let N0 := max common.choose (max scalar.choose errors.2.choose)
  refine And.intro errors.1 (Exists.intro N0 (And.intro
    (le_trans common.choose_spec.1 (le_max_left _ _)) ?_))
  intro Iota instF instD instN hn T S U hCard q a hq ha hA hSize hRow hCol hNonneg hUpper hNorm
  have hnCommon : common.choose <= Fintype.card Iota := le_trans (le_max_left _ _) hn
  have hnScalar : scalar.choose <= Fintype.card Iota :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnErrors : errors.2.choose <= Fintype.card Iota :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hN32 : 32 <= Fintype.card Iota := le_trans common.choose_spec.1 hnCommon
  have hN4 : 4 <= Fintype.card Iota := le_trans (by norm_num) hN32
  have hN0 : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hqValue : q = 1 / (Fintype.card Iota : Real) := by
    calc
      _ = ((Fintype.card Iota : Real) * q) / (Fintype.card Iota : Real) := by
        field_simp [ne_of_gt hN0]
      _ = _ := by rw [hq]
  have hQSquare : q ^ 2 = 1 / (Fintype.card Iota : Real) ^ 2 := by
    rw [hqValue, div_pow, one_pow]
  have hRange := scalar.choose_spec.2 (Fintype.card Iota) hnScalar U.card a hSize ha hA
  have hHalfCast := hRange.2.1
  rw [Nat.cast_sub (Finset.card_le_univ U)] at hHalfCast
  have hHalf : (U.card : Real) <= (Fintype.card Iota : Real) / 2 := by
    linarith only [hHalfCast]
  have hStrong : (U.card : Real) * (a / delta) ^ 3 * q <= 1 / 10000 := by
    rw [hqValue]
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hRange.1
  have hErrorRange := errors.2.choose_spec.2 (Fintype.card Iota) hnErrors U.card a hSize ha hA
  have hSmall : 100 * (1 + (U.card : Real)) ^ 2 * (a / delta) ^ 2 * q +
      hamiltonianMinorLogBudget delta (U.card : Real) a * q ^ 2 <= 1 := by
    rw [hqValue]
    simpa only [div_eq_mul_inv, div_pow, one_pow, one_mul, mul_one, inv_pow] using hErrorRange.1
  have hData := common.choose_spec.2 Iota hnCommon T S U hCard q a hq ha hA hSize
    hRow hCol hNonneg hUpper hNorm
  let z := Classical.choose hData.2.2.2.2
  have hz := Classical.choose_spec hData.2.2.2.2
  have hMinor := stochastic_actual_minor_two_power_budget T S U hCard q a delta hN4 hq ha
    hDelta hDelta1 hHalf hRow hCol hNonneg hUpper hNorm hStrong z hz.1 hz.2.1
    hz.2.2.1 hz.2.2.2.1 hData.1 hz.2.2.2.2.1 hData.2.1 hz.2.2.2.2.2.1 hSmall
  refine And.intro hData.2.1.2.2 ?_
  calc
    _ <= hamiltonianMinorTwoPowerBudget delta (U.card : Real) a * q ^ 2 := hMinor
    _ = hamiltonianMinorTwoPowerBudget delta (U.card : Real) a /
        (Fintype.card Iota : Real) ^ 2 := by rw [hQSquare]; ring
    _ <= _ := hErrorRange.2

end PrimeFactorOscillations
