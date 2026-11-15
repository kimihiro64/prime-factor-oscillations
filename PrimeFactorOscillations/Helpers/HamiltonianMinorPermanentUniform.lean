/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolylogRange
import PrimeFactorOscillations.Helpers.HamiltonianPermanentPositivity
import PrimeFactorOscillations.Helpers.HamiltonianRepairedPermanentTransport

/-! # A common complete permanent expansion for every repaired minor

A single threshold covers all admissible original kernels and all
independent polylogarithmic deleted supports. One physical witness
is shared by the permanent, correction and local-cost consumers.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPermanentRelativeCorrectionBound {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix J J Real) (q a delta : Real) : Prop :=
  (abs ((((Fintype.card J : Real) ^ Fintype.card J /
      ((Fintype.card J).factorial : Real)) * weightedPermutationSum T) /
        realGramDeterminantFactor (centeredKernel T q) 1 -
        (1 + stochasticPermanentFirstCorrection T q)) <=
      (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta /
        (Fintype.card J : Real) ^ 2) /\
  abs (stochasticPermanentFirstCorrection T q) <=
    21 * a ^ 2 / (delta ^ 3 * (Fintype.card J : Real))

universe u

theorem stochastic_minor_permanent_common_uniform_range (delta K : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
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
          let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
          let J : Finset Iota := Compl.compl U
          let qNew := q / (1 - (U.card : Real) * q)
          hamiltonianPermanentRelativeCorrectionBound T q a delta /\
          hamiltonianPermanentPositiveData T q /\
          2 <= Fintype.card J /\ (Fintype.card J : Real) * qNew = 1 /\
          exists z : R -> Real,
            norm z <= 20 * (U.card : Real) * a * q / delta /\
            norm (z - (fun i : R =>
              (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
                5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / delta ^ 3 /\
            (forall i : R, 0 < 1 + z i) /\
            (forall i : R, (1 + z i) *
              (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1) /\
            hamiltonianPermanentRelativeCorrectionBound
              (hamiltonianRepairedSquareKernel T S U hCard z) qNew (2 * a) (delta / 2) /\
            hamiltonianPermanentPositiveData (hamiltonianRepairedSquareKernel T S U hCard z) qNew /\
            abs (stochasticPermanentFirstCorrection
                (hamiltonianRepairedSquareKernel T S U hCard z) qNew -
                  stochasticPermanentFirstCorrection T q) <=
              500000 * (U.card : Real) * (a / delta) ^ 6 * q ^ 2 /\
            finitePermutationSum (hamiltonianRepairedSquareKernel T S U hCard z) =
              Real.exp (Finset.univ.sum (fun i => Real.log (1 + z i))) *
                rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) := by
  have hHalf : 0 < delta / 2 := div_pos hDelta (by norm_num)
  have hHalf1 : delta / 2 <= 1 := by linarith only [hDelta1]
  let original := stochastic_permanent_relative_correction_fintype_uniform.{u} delta K hDelta hDelta1
  let smaller := stochastic_permanent_relative_correction_fintype_uniform.{u}
    (delta / 2) (K + 1) hHalf hHalf1
  let positiveOriginal := stochastic_permanent_positive_polylog_uniform.{u} delta K hDelta hDelta1 hK
  let positiveSmaller := stochastic_permanent_positive_polylog_uniform.{u}
    (delta / 2) (K + 1) hHalf hHalf1 (by linarith only [hK])
  let scalar := hamiltonian_minor_polylog_uniform_range delta K
    (max smaller.choose positiveSmaller.choose) hDelta hDelta1 hK
  let N0 := max original.choose (max scalar.choose positiveOriginal.choose)
  refine Exists.intro N0 (And.intro
    (le_trans scalar.choose_spec.1 (le_trans (le_max_left _ _) (le_max_right _ _))) ?_)
  intro Iota instF instD instN hn T S U hCard q a hq ha hA hSize hRow hCol hNonneg hUpper hNorm
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let J : Finset Iota := Compl.compl U
  let qNew := q / (1 - (U.card : Real) * q)
  have hnScalar : scalar.choose <= Fintype.card Iota :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnPositive : positiveOriginal.choose <= Fintype.card Iota :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hN32 : 32 <= Fintype.card Iota := le_trans scalar.choose_spec.1 hnScalar
  have hN4 : 4 <= Fintype.card Iota := le_trans (by norm_num) hN32
  have hN0 : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hqValue : q = 1 / (Fintype.card Iota : Real) := by
    calc
      _ = ((Fintype.card Iota : Real) * q) / (Fintype.card Iota : Real) := by
        field_simp [ne_of_gt hN0]
      _ = _ := by rw [hq]
  have hData := scalar.choose_spec.2 (Fintype.card Iota) hnScalar U.card a hSize ha hA
  have hGap : 1 - (1 - delta) = delta := by ring
  have hRho : 1 - delta < 1 := by linarith only [hDelta]
  have hStrong : (U.card : Real) * (a / (1 - (1 - delta))) ^ 3 * q <= 1 / 10000 := by
    rw [hGap, hqValue]
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hData.1
  have hRepair := stochastic_repaired_square_exists T S U hCard q a (1 - delta)
    hN4 hq ha hRow hCol hNonneg hUpper hNorm hRho hStrong
  simp only [hGap] at hRepair
  let z := Classical.choose hRepair.2.2
  have hz := Classical.choose_spec hRepair.2.2
  have hJCard : Fintype.card J = Fintype.card Iota - U.card := by
    simp only [J, Fintype.card_coe, Finset.card_compl]
  have hNewBothSize : max smaller.choose positiveSmaller.choose <= Fintype.card J := by
    rw [hJCard]
    exact hData.2.2.1
  have hNewSize : smaller.choose <= Fintype.card J := le_trans (le_max_left _ _) hNewBothSize
  have hPositiveNewSize : positiveSmaller.choose <= Fintype.card J :=
    le_trans (le_max_right _ _) hNewBothSize
  have hNewCap : 2 * a <= (Real.log (Fintype.card J : Real)) ^ (K + 1) := by
    rw [hJCard]
    exact hData.2.2.2.2
  have hOld : hamiltonianPermanentRelativeCorrectionBound T q a delta :=
    original.choose_spec.2 Iota (le_trans (le_max_left _ _) hn) T q a hq ha hA
      hRow hCol hNonneg hUpper hNorm
  have hOldPositive : hamiltonianPermanentPositiveData T q :=
    positiveOriginal.choose_spec.2 Iota hnPositive T q a hq ha hA
      hRow hCol hNonneg hUpper hNorm
  have hNew : hamiltonianPermanentRelativeCorrectionBound
      (hamiltonianRepairedSquareKernel T S U hCard z) qNew (2 * a) (delta / 2) :=
    smaller.choose_spec.2 J hNewSize (hamiltonianRepairedSquareKernel T S U hCard z)
      qNew (2 * a) hRepair.2.1 (by linarith only [ha]) hNewCap
      hz.2.2.2.2.2.1.1 hz.2.2.2.2.2.1.2 hz.2.2.2.2.1
      hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2
  have hNewPositive : hamiltonianPermanentPositiveData
      (hamiltonianRepairedSquareKernel T S U hCard z) qNew :=
    positiveSmaller.choose_spec.2 J hPositiveNewSize (hamiltonianRepairedSquareKernel T S U hCard z)
      qNew (2 * a) hRepair.2.1 (by linarith only [ha]) hNewCap
      hz.2.2.2.2.2.1.1 hz.2.2.2.2.2.1.2 hz.2.2.2.2.1
      hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2
  have hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - (1 - delta)) := by
    simpa only [hGap] using hz.1
  have hCorrection := stochastic_repaired_first_correction_comparison T S U hCard q a
    (1 - delta) hN4 hq ha hRow hCol hNonneg hUpper hNorm hRho hStrong z hZ
  simp only [hGap] at hCorrection
  refine And.intro hOld (And.intro hOldPositive
    (And.intro hRepair.1 (And.intro hRepair.2.1 (Exists.intro z ?_))))
  exact And.intro hz.1 (And.intro hz.2.1 (And.intro hz.2.2.1
    (And.intro hz.2.2.2.1 (And.intro hNew (And.intro hNewPositive (And.intro hCorrection
      (hamiltonian_repaired_permanent_transport T S U hCard z hz.2.2.1)))))))

end PrimeFactorOscillations
