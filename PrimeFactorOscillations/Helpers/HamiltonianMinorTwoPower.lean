/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorExponentialTransfer
import PrimeFactorOscillations.Helpers.HamiltonianMinorFirstOrderBudget
import PrimeFactorOscillations.Helpers.HamiltonianMinorLogAssembly

/-! # The actual two-power minor estimate

The complete logarithmic identity is exponentiated with its signed
first-order correction. Every analytic error remains in the budget.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianMinorTwoPowerBudget (delta r a : Real) : Real :=
  20000 * (1 + r) ^ 4 * (a / delta) ^ 4 + 3 * hamiltonianMinorLogBudget delta r a

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_actual_minor_two_power_budget
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a delta : Real) (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hHalf : (U.card : Real) <= (Fintype.card Iota : Real) / 2)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hStrong : (U.card : Real) * (a / delta) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / delta)
    (hClose : norm (z - (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
      (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / delta ^ 3)
    (hPos : forall i, 0 < 1 + z i)
    (hScaling : forall i, (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1)
    (hOldBound : hamiltonianPermanentRelativeCorrectionBound T q a delta)
    (hNewBound : hamiltonianPermanentRelativeCorrectionBound
      (hamiltonianRepairedSquareKernel T S U hCard z)
        (q / (1 - (U.card : Real) * q)) (2 * a) (delta / 2))
    (hOldPositive : hamiltonianPermanentPositiveData T q)
    (hNewPositive : hamiltonianPermanentPositiveData
      (hamiltonianRepairedSquareKernel T S U hCard z) (q / (1 - (U.card : Real) * q)))
    (hSmall : 100 * (1 + (U.card : Real)) ^ 2 * (a / delta) ^ 2 * q +
      hamiltonianMinorLogBudget delta (U.card : Real) a * q ^ 2 <= 1) :
    abs ((rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) ^ 2 - (1 + hamiltonianMinorFirstOrder T S U q)) <=
        hamiltonianMinorTwoPowerBudget delta (U.card : Real) a * q ^ 2 := by
  let r : Real := U.card
  let p := a / delta
  let alpha := hamiltonianMinorFirstOrder T S U q
  let eps := hamiltonianMinorLogBudget delta r a * q ^ 2
  let t := rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
    weightedPermutationSum T
  have hLog := stochastic_actual_minor_log_budget T S U hCard q a delta hN hq ha
    hDelta hDelta1 hHalf hRow hCol hNonneg hUpper hNorm hStrong z hZ hClose
    hPos hScaling hOldBound hNewBound hOldPositive hNewPositive
  have ht : 0 < t := div_pos hLog.1 hOldPositive.2.2
  have hLogError : abs (2 * Real.log t - alpha) <= eps := hLog.2
  have hAlpha := stochastic_minor_first_order_budget T S U hCard q a delta hq ha
    hDelta hDelta1 hRow hCol hNonneg hUpper hNorm
  change abs alpha <= 100 * (1 + r) ^ 2 * p ^ 2 * q at hAlpha
  have hEps0 : 0 <= eps := le_trans (abs_nonneg _) hLogError
  have hRange : abs alpha + eps <= 1 := by linarith only [hAlpha, hSmall]
  have hEps1 : eps <= 1 := by linarith only [hRange, abs_nonneg alpha]
  have hExp := hamiltonian_minor_exponential_transfer t alpha eps ht hEps0 hEps1 hLogError hRange
  have hSquare := mul_le_mul hAlpha hAlpha (abs_nonneg alpha)
    (le_trans (abs_nonneg alpha) hAlpha)
  rw [<- pow_two, sq_abs] at hSquare
  change abs (t ^ 2 - (1 + alpha)) <= hamiltonianMinorTwoPowerBudget delta r a * q ^ 2
  calc
    _ <= 2 * alpha ^ 2 + 3 * eps := hExp
    _ <= 2 * (100 * (1 + r) ^ 2 * p ^ 2 * q) ^ 2 + 3 * eps := by
      nlinarith only [hSquare]
    _ = _ := by dsimp only [hamiltonianMinorTwoPowerBudget, p, eps]; ring

end PrimeFactorOscillations
