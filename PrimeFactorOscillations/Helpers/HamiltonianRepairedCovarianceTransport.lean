/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCorrectionTrace
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareExists
import PrimeFactorOscillations.Helpers.HamiltonianStochasticFirstCorrectionComparison

/-! # Exact transport of every signed covariance correction

The actual inverse, diagonal, triple, cubic and full squared trace are
preserved together by the retained coordinate equivalence.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
  [Fintype Jota] [DecidableEq Jota]

private theorem hamiltonian_double_sum_reindex (f : Iota -> Iota -> Real)
    (e : Equiv Jota Iota) :
    Finset.univ.sum (fun i : Jota => Finset.univ.sum (fun j : Jota => f (e i) (e j))) =
      Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota => f i j)) := by
  calc
    _ = Finset.univ.sum (fun i : Jota => Finset.univ.sum (fun j : Iota => f (e i) j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem hamiltonian_resolvent_covariance_reindex (M : Matrix Iota Iota Real)
    (e : Equiv Jota Iota) :
    resolventCovariance (M.submatrix e e) = (resolventCovariance M).submatrix e e := by
  have hAdd : (1 : Matrix Jota Jota Real) + M.submatrix e e =
      ((1 : Matrix Iota Iota Real) + M).submatrix e e := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, e.injective.eq_iff]
  have hInv : Ring.inverse (((1 : Matrix Iota Iota Real) + M).submatrix e e) =
      (Ring.inverse ((1 : Matrix Iota Iota Real) + M)).submatrix e e := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      Matrix.inv_submatrix_equiv ((1 : Matrix Iota Iota Real) + M) e e
  unfold resolventCovariance
  rw [hAdd, hInv, Matrix.submatrix_mul_equiv]

theorem hamiltonian_covariance_trace_correction_reindex (M : Matrix Iota Iota Real)
    (e : Equiv Jota Iota) (n : Real) :
    covarianceTraceCorrection (M.submatrix e e) n = covarianceTraceCorrection M n := by
  have hTrace : Matrix.trace (M.submatrix e e) = Matrix.trace M := by
    change Finset.univ.sum (fun i : Jota => M (e i) (e i)) =
      Finset.univ.sum (fun i : Iota => M i i)
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hSquareTrace : Matrix.trace (M.submatrix e e * M.submatrix e e) = Matrix.trace (M * M) := by
    rw [Matrix.submatrix_mul_equiv]
    change Finset.univ.sum (fun i : Jota => (M * M) (e i) (e i)) =
      Finset.univ.sum (fun i : Iota => (M * M) i i)
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hDiagonal : covarianceDiagonalEnergy (M.submatrix e e) = covarianceDiagonalEnergy M := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hTriple : covarianceTriple (M.submatrix e e) = covarianceTriple M := by
    exact hamiltonian_double_sum_reindex (fun i j => M i i * M j j * M i j) e
  have hCubic : covarianceCubic (M.submatrix e e) = covarianceCubic M := by
    exact hamiltonian_double_sum_reindex (fun i j => M i j ^ 3) e
  unfold covarianceTraceCorrection covarianceCorrection
  rw [hTrace, hSquareTrace, hDiagonal, hTriple, hCubic]

theorem hamiltonian_repaired_covariance_reindex
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew : Real) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let e := hamiltonianRepairedSquareEquiv S U hCard
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    resolventCovariance (bipartiteLift
      (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew)) =
      ((HR + E - 1) * Ring.inverse (HR + E)).submatrix e e := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  have hTransport := hamiltonian_repaired_centered_reindex T S U hCard z q qNew
  have hOne : (1 : Matrix R R Real) + (HR + E - 1) = HR + E := by abel
  change resolventCovariance _ = _
  rw [<- hTransport, hamiltonian_resolvent_covariance_reindex]
  unfold resolventCovariance
  rw [hOne]

theorem hamiltonian_repaired_first_correction_transport
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew rhoNew : Real)
    (hN : 2 <= Fintype.card (Compl.compl U : Finset Iota))
    (hNorm : norm (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) <= rhoNew)
    (hRho : rhoNew < 1) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    stochasticPermanentFirstCorrection (hamiltonianRepairedSquareKernel T S U hCard z) qNew =
      covarianceTraceCorrection ((HR + E - 1) * Ring.inverse (HR + E))
        (Fintype.card (Compl.compl U : Finset Iota) : Real) := by
  rw [stochasticPermanentFirstCorrection_trace_formula _ qNew rhoNew hN hNorm hRho,
    hamiltonian_repaired_covariance_reindex T S U hCard z q qNew,
    hamiltonian_covariance_trace_correction_reindex]


theorem stochastic_repaired_first_correction_comparison [Nonempty Iota]
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho)) :
    abs (stochasticPermanentFirstCorrection (hamiltonianRepairedSquareKernel T S U hCard z)
        (q / (1 - (U.card : Real) * q)) - stochasticPermanentFirstCorrection T q) <=
      500000 * (U.card : Real) * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  have hJ2 : 2 <= Fintype.card (Compl.compl U : Finset Iota) :=
    (stochastic_repaired_square_exists T S U hCard q a rho hN hq ha
      hRow hCol hNonneg hUpper hNorm hRho hSmall).1
  have hGap := stochastic_repaired_square_gap T S U hCard q a rho hq ha
    hNonneg hUpper hNorm hRho hSmall z hZ
  have hNewRho : 1 - (1 - rho) / 2 < 1 := by linarith only [hRho]
  have hRank : (Fintype.card (Compl.compl U : Finset Iota) : Real) =
      (Fintype.card Iota : Real) - (U.card : Real) := by
    simp only [Fintype.card_coe, Finset.card_compl, Nat.cast_sub (Finset.card_le_univ U)]
  rw [hamiltonian_repaired_first_correction_transport T S U hCard z q
    (q / (1 - (U.card : Real) * q)) (1 - (1 - rho) / 2) hJ2 hGap hNewRho, hRank]
  exact stochastic_repaired_trace_correction_comparison T S U hCard q a rho hN hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall z hZ

end PrimeFactorOscillations
