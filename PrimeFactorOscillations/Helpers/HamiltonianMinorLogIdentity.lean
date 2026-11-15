/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorFactorialNormalizer
import PrimeFactorOscillations.Helpers.HamiltonianPermanentPositivity
import PrimeFactorOscillations.Helpers.HamiltonianRepairedPermanentTransport

/-! # Exact logarithmic identity for the actual complementary permanent

The physical scaling, factorial normalization, Gaussian determinant
and full normalized correction remain in one identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_log_normalized_permanent
    (T : Matrix Iota Iota Real) (q : Real) (hN : 1 <= Fintype.card Iota)
    (hPositive : hamiltonianPermanentPositiveData T q) :
    Real.log (hamiltonianNormalizedPermanent T q) =
      Real.log (weightedPermutationSum T) -
        hamiltonianLogPermanentNormalizer (Fintype.card Iota) -
          Real.log (realGramDeterminantFactor (centeredKernel T q) 1) := by
  let n := Fintype.card Iota
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  have hN0 : 0 < (n : Real) := Nat.cast_pos.mpr (show 0 < n by dsimp only [n]; omega)
  have hNne : Not ((n : Real) = 0) := ne_of_gt hN0
  have hFactorial : Not ((n.factorial : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hPower : Not ((n : Real) ^ n = 0) := pow_ne_zero n hNne
  have hCoefficient : Not (((n : Real) ^ n / (n.factorial : Real)) = 0) :=
    div_ne_zero hPower hFactorial
  have hPer : Not (weightedPermutationSum T = 0) := ne_of_gt hPositive.2.2
  have hD : Not (D = 0) := by
    have h : (1 : Real) <= D := hPositive.2.1
    linarith only [h]
  change Real.log ((((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T) / D) = _
  rw [Real.log_div (mul_ne_zero hCoefficient hPer) hD,
    Real.log_mul hCoefficient hPer, Real.log_div hPower hFactorial, Real.log_pow]
  unfold hamiltonianLogPermanentNormalizer
  ring

theorem hamiltonian_actual_minor_log_identity
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew : Real) (hN : 1 <= Fintype.card Iota)
    (hM : 1 <= Fintype.card (Compl.compl U : Finset Iota))
    (hPos : forall i, 0 < 1 + z i)
    (hOld : hamiltonianPermanentPositiveData T q)
    (hNew : hamiltonianPermanentPositiveData (hamiltonianRepairedSquareKernel T S U hCard z) qNew) :
    let TNew := hamiltonianRepairedSquareKernel T S U hCard z
    let scaling := Finset.univ.sum (fun i => Real.log (1 + z i))
    let n := Fintype.card Iota
    let m := Fintype.card (Compl.compl U : Finset Iota)
    0 < rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /\
    2 * Real.log (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) =
      -2 * scaling + 2 * (hamiltonianLogPermanentNormalizer m - hamiltonianLogPermanentNormalizer n) +
        2 * (Real.log (realGramDeterminantFactor (centeredKernel TNew qNew) 1) -
          Real.log (realGramDeterminantFactor (centeredKernel T q) 1)) +
        2 * (Real.log (hamiltonianNormalizedPermanent TNew qNew) -
          Real.log (hamiltonianNormalizedPermanent T q)) := by
  let TNew := hamiltonianRepairedSquareKernel T S U hCard z
  let scaling := Finset.univ.sum (fun i => Real.log (1 + z i))
  let minor := rectangularMinorPermanent T (Compl.compl S) (Compl.compl U)
  have hScale : weightedPermutationSum TNew = Real.exp scaling * minor :=
    hamiltonian_repaired_permanent_transport T S U hCard z hPos
  have hMinor : 0 < minor := by
    by_contra h
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos scaling)) (le_of_not_gt h)
    rw [<- hScale] at hNonpos
    exact not_le_of_gt hNew.2.2 hNonpos
  have hLogScale : Real.log (weightedPermutationSum TNew) = scaling + Real.log minor := by
    have h := congrArg Real.log hScale
    rw [Real.log_mul (Real.exp_ne_zero scaling) (ne_of_gt hMinor), Real.log_exp] at h
    exact h
  have hLogOld := hamiltonian_log_normalized_permanent T q hN hOld
  have hLogNew := hamiltonian_log_normalized_permanent TNew qNew hM hNew
  refine And.intro hMinor ?_
  change 2 * Real.log (minor / weightedPermutationSum T) =
    -2 * scaling +
      2 * (hamiltonianLogPermanentNormalizer (Fintype.card (Compl.compl U : Finset Iota)) -
        hamiltonianLogPermanentNormalizer (Fintype.card Iota)) +
      2 * (Real.log (realGramDeterminantFactor (centeredKernel TNew qNew) 1) -
        Real.log (realGramDeterminantFactor (centeredKernel T q) 1)) +
      2 * (Real.log (hamiltonianNormalizedPermanent TNew qNew) -
        Real.log (hamiltonianNormalizedPermanent T q))
  rw [Real.log_div (ne_of_gt hMinor) (ne_of_gt hOld.2.2)]
  linarith only [hLogOld, hLogNew, hLogScale]

end PrimeFactorOscillations
