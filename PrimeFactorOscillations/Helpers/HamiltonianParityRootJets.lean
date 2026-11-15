/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianParityRootRegularization

/-! # Actual first jets at the regularized parity root

The full determinant trace and matrix inverse derivative are applied
to the actual regularization. All parity and constant contributions
remain. No physical inverse is evaluated at its singular root.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_det_one_add_hasDerivAt (E : Matrix Iota Iota Real) :
    HasDerivAt (fun t : Real => Matrix.det (1 + HSMul.hSMul t E)) (Matrix.trace E) 0 := by
  let p := principalMinorGeneratingPolynomial E
  let Q := p.divX.divX
  have hFormula (t : Real) :
      Matrix.det (1 + HSMul.hSMul t E) =
        1 + Matrix.trace E * t + t ^ 2 * Polynomial.eval t Q := by
    simpa only [Q, p, principalMinorGeneratingPolynomial, mul_comm] using!
      (Matrix.det_one_add_smul t E)
  have hIdentity : (fun t : Real => Matrix.det (1 + HSMul.hSMul t E)) =
      (fun t : Real => 1 + Matrix.trace E * t + t ^ 2 * Polynomial.eval t Q) :=
    funext hFormula
  rw [hIdentity]
  have hId := hasDerivAt_id (0 : Real)
  have hLin := (hasDerivAt_const (0 : Real) (Matrix.trace E)).mul hId
  have hRest := (hId.pow 2).mul (Q.hasDerivAt (0 : Real))
  have hAll := ((hasDerivAt_const (0 : Real) (1 : Real)).add hLin).add hRest
  simpa [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq] using! hAll

theorem hamiltonian_affine_inverse_hasDerivAt
    (M P : Matrix Iota Iota Real) (hUnit : IsUnit M) :
    HasDerivAt (fun t : Real => Ring.inverse (M - HSMul.hSMul t P))
      (Ring.inverse M * P * Ring.inverse M) 0 := by
  let u : Units (Matrix Iota Iota Real) := Classical.choose hUnit
  have hu : (u : Matrix Iota Iota Real) = M := Classical.choose_spec hUnit
  have hUM : ((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real) * M = 1 := by
    rw [<- hu]
    exact u.inv_val
  have hUInverse : ((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real) =
      Ring.inverse M := by
    calc
      _ = ((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real) *
          (M * Ring.inverse M) := by rw [Ring.mul_inverse_cancel M hUnit, mul_one]
      _ = ((((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real) * M) *
          Ring.inverse M) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hUM, one_mul]
  have hInv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight Real (Matrix Iota Iota Real)
        ((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real)
        ((Inv.inv u : Units (Matrix Iota Iota Real)) : Matrix Iota Iota Real))
      (u : Matrix Iota Iota Real) := hasFDerivAt_ringInverse u
  rw [hu, hUInverse] at hInv
  have hFamily : HasDerivAt (fun t : Real => M - HSMul.hSMul t P) (-P) 0 := by
    simpa only [Pi.sub_apply, id_eq, one_smul, zero_sub] using!
      (hasDerivAt_const (0 : Real) M).sub ((hasDerivAt_id (0 : Real)).smul_const P)
  have hComp := hInv.comp_hasDerivAt_of_eq (0 : Real) hFamily (by simp)
  change HasDerivAt (fun t : Real => Ring.inverse (M - HSMul.hSMul t P))
    (-(Ring.inverse M * (-P) * Ring.inverse M)) 0 at hComp
  simpa only [mul_neg, neg_mul, neg_neg] using hComp

theorem hamiltonian_affine_determinant_hasDerivAt
    (M P : Matrix Iota Iota Real) (hUnit : IsUnit M) :
    HasDerivAt (fun t : Real => Matrix.det (M - HSMul.hSMul t P))
      (-(Matrix.det M) * Matrix.trace (Ring.inverse M * P)) 0 := by
  let E := -(Ring.inverse M * P)
  have hME : M * E = -P := by
    dsimp only [E]
    rw [mul_neg, <- mul_assoc, Ring.mul_inverse_cancel M hUnit, one_mul]
  have hFactor (t : Real) : M - HSMul.hSMul t P = M * (1 + HSMul.hSMul t E) := by
    rw [mul_add, mul_one, Matrix.mul_smul, hME, smul_neg, sub_eq_add_neg]
  have hIdentity : (fun t : Real => Matrix.det (M - HSMul.hSMul t P)) =
      (fun t : Real => Matrix.det M * Matrix.det (1 + HSMul.hSMul t E)) := by
    funext t
    rw [hFactor, Matrix.det_mul]
  have hTrace : Matrix.trace E = -Matrix.trace (Ring.inverse M * P) := by
    dsimp only [E]
    rw [Matrix.trace_neg]
  rw [hIdentity]
  have h := (hasDerivAt_const (0 : Real) (Matrix.det M)).mul
    (hamiltonian_det_one_add_hasDerivAt E)
  simpa only [Pi.mul_apply, zero_mul, zero_add, hTrace, mul_neg, neg_mul] using! h

theorem hamiltonian_parity_projection_traces (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) :
    Matrix.trace (hamiltonianParityProjection (Iota := Iota) q) = 1 /\
    Matrix.trace (hamiltonianRepairProjection (Iota := Iota) q) = 3 / 2 := by
  constructor
  case left =>
    change Finset.univ.sum (fun i : Sum Iota Iota => hamiltonianParityProjection q i i) = 1
    simp only [Fintype.sum_sum_type, hamiltonianParityProjection, hamiltonianParitySign,
      mul_one, mul_neg, neg_mul, neg_neg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith only [hq]
  case right =>
    change Finset.univ.sum (fun i : Sum Iota Iota => hamiltonianRepairProjection q i i) = 3 / 2
    simp only [Fintype.sum_sum_type, hamiltonianRepairProjection, hamiltonianParitySign,
      mul_one, mul_neg, neg_mul, neg_neg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith only [hq]

theorem stochastic_regularized_root_inverse_product (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    Ring.inverse (hamiltonianParityRegularizedKernel T q 0) * bipartiteLift T =
      1 - hamiltonianRepairKernel T q - hamiltonianParityProjection q -
        hamiltonianParityProjection q := by
  have hData := stochastic_regularized_kernel_inverse T q rho hq hRow hCol hNorm hRho
  rw [hData.2, add_mul,
    stochastic_repair_kernel_mul_left T q rho hq hRow hCol hNorm hRho,
    stochastic_parity_projection_mul_kernel T q hRow hCol]
  abel

theorem stochastic_regularized_root_inverse_trace (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    Matrix.trace (Ring.inverse (hamiltonianParityRegularizedKernel T q 0) * bipartiteLift T) =
      Matrix.trace (resolventCovariance (bipartiteLift (centeredKernel T q))) - 1 / 2 := by
  have hTraces := hamiltonian_parity_projection_traces (Iota := Iota) q hq
  rw [stochastic_regularized_root_inverse_product T q rho hq hRow hCol hNorm hRho,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    hamiltonianRepairKernel_covariance T q rho hNorm hRho,
    Matrix.trace_sub, Matrix.trace_sub, hTraces.1, hTraces.2]
  ring

theorem stochastic_regularized_determinant_hasDerivAt (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    HasDerivAt (fun t : Real => Matrix.det (hamiltonianParityRegularizedKernel T q t))
      (Matrix.det (hamiltonianParityRegularizedKernel T q 0) *
        (1 / 2 - Matrix.trace (resolventCovariance (bipartiteLift (centeredKernel T q))))) 0 := by
  let M := hamiltonianParityRegularizedKernel T q 0
  have hUnit := (stochastic_regularized_kernel_inverse T q rho hq hRow hCol hNorm hRho).1
  have h := hamiltonian_affine_determinant_hasDerivAt M (bipartiteLift T) hUnit
  have hFamily : (fun t : Real => M - HSMul.hSMul t (bipartiteLift T)) =
      hamiltonianParityRegularizedKernel T q := by
    funext t
    simp only [M, hamiltonianParityRegularizedKernel, zero_smul, sub_zero]
  have hFamilyPoint (t : Real) := congrFun hFamily t
  simp only [hFamilyPoint] at h
  have hTrace := stochastic_regularized_root_inverse_trace T q rho hq hRow hCol hNorm hRho
  dsimp only [M] at h
  rw [hTrace] at h
  convert h using 1 <;> ring

theorem stochastic_regularized_covariance_value (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
        Ring.inverse (hamiltonianParityRegularizedKernel T q 0) =
      resolventCovariance (bipartiteLift (centeredKernel T q)) +
        averagingKernel (Iota := Sum Iota Iota) (q / 4) := by
  rw [(stochastic_regularized_kernel_inverse T q rho hq hRow hCol hNorm hRho).2,
    hamiltonianRepairKernel_covariance T q rho hNorm hRho]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.add_apply, hamiltonianRepairProjection,
    hamiltonianParityProjection, averagingKernel]
  ring

theorem stochastic_regularized_covariance_hasDerivAt (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    HasDerivAt (fun t : Real =>
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
        Ring.inverse (hamiltonianParityRegularizedKernel T q t))
      ((hamiltonianRepairKernel T q) ^ 2 - hamiltonianRepairKernel T q +
        hamiltonianParityProjection q) 0 := by
  let M := hamiltonianParityRegularizedKernel T q 0
  let P := bipartiteLift T
  let K := hamiltonianRepairKernel T q
  let S := hamiltonianParityProjection (Iota := Iota) q
  let R := Ring.inverse M
  have hData := stochastic_regularized_kernel_inverse T q rho hq hRow hCol hNorm hRho
  have hInv := hamiltonian_affine_inverse_hasDerivAt M P hData.1
  have hFamily : (fun t : Real => M - HSMul.hSMul t P) =
      hamiltonianParityRegularizedKernel T q := by
    funext t
    simp only [M, P, hamiltonianParityRegularizedKernel, zero_smul, sub_zero]
  have hFamilyPoint (t : Real) := congrFun hFamily t
  simp only [hFamilyPoint] at hInv
  have hProduct : R * P = 1 - K - S - S :=
    stochastic_regularized_root_inverse_product T q rho hq hRow hCol hNorm hRho
  have hKS : K * S = 0 := stochastic_repair_kernel_parity T q rho hq hRow hCol hNorm hRho
  have hSK : S * K = 0 := stochastic_parity_repair_kernel T q rho hq hRow hCol hNorm hRho
  have hSS : S * S = S := hamiltonian_parity_projection_idempotent q hq
  have hR : R = K + S := hData.2
  have hQuad : R * P * R = K - K ^ 2 - S := by
    calc
      _ = (1 - K - S - S) * (K + S) := by rw [hProduct, hR]
      _ = _ := by
        simp only [mul_add, sub_mul, one_mul, hKS, hSK, hSS, sub_zero, pow_two]
        abel
  have hSign : -(R * P * R) = K ^ 2 - K + S := by rw [hQuad]; abel
  have h := (hasDerivAt_const (0 : Real)
    (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)).sub hInv
  change HasDerivAt _ (0 - R * P * R) 0 at h
  rw [zero_sub, hSign] at h
  exact h

end PrimeFactorOscillations
