/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import PrimeFactorOscillations.Helpers.HamiltonianClearedRootDerivative
import PrimeFactorOscillations.Helpers.HamiltonianParityRootJets
import PrimeFactorOscillations.Helpers.HamiltonianParityRootNormalization
import PrimeFactorOscillations.Helpers.HamiltonianPhysicalOccupancy

/-! # Exact signed occupancy at the actual parity root

The cleared actual coordinate polynomials are differentiated through
their continuous regularization. Both ordered off-diagonal products
and the derivative of the parity compensation remain.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_matrix_entry_hasDerivAt
    (F : Real -> Matrix Iota Iota Real) (FPrime : Matrix Iota Iota Real)
    (hF : HasDerivAt F FPrime 0) (a b : Iota) :
    HasDerivAt (fun t : Real => F t a b) (FPrime a b) 0 := by
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hF a)) b

theorem stochastic_regularized_root_unit_neighborhood
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    Filter.Eventually (fun t : Real =>
      IsUnit (hamiltonianParityRegularizedKernel T q t)) (nhds 0) := by
  let M := hamiltonianParityRegularizedKernel T q 0
  have hUnit := (stochastic_regularized_kernel_inverse T q rho hq hRow hCol hNorm hRho).1
  have hAffine : Continuous (fun t : Real => M - HSMul.hSMul t (bipartiteLift T)) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hAt : IsUnit (M - HSMul.hSMul (0 : Real) (bipartiteLift T)) := by
    simpa only [zero_smul, sub_zero] using hUnit
  have hNear := hAffine.continuousAt.eventually (Units.isOpen.mem_nhds hAt)
  have hFamilyPoint (t : Real) :
      M - HSMul.hSMul t (bipartiteLift T) = hamiltonianParityRegularizedKernel T q t := by
    simp only [M, hamiltonianParityRegularizedKernel, zero_smul, sub_zero]
  simpa only [hFamilyPoint] using! hNear

theorem hamiltonian_polynomial_reverse_hasDerivAt (p : Polynomial Real) :
    HasDerivAt (fun t : Real => Polynomial.eval (1 - t) p)
      (-Polynomial.eval 1 p.derivative) 0 := by
  have hSub : HasDerivAt (fun t : Real => 1 - t) (-1 : Real) 0 := by
    simpa using! (hasDerivAt_const (0 : Real) (1 : Real)).sub (hasDerivAt_id (0 : Real))
  have h := (p.hasDerivAt (1 - (0 : Real))).comp (0 : Real) hSub
  simpa [Function.comp_def] using! h

theorem stochastic_coordinate_minor_moment_root
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) (a : Sum Iota Iota) :
    let d := Matrix.det ((1 : Matrix Iota Iota Real) -
      (centeredKernel T q).transpose * centeredKernel T q)
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
      Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    hamiltonianCoordinateMinorMoment (bipartiteLift T) a =
      d * (A a a + (3 / 2 + Matrix.trace G) * hamiltonianParityProjection q a a) := by
  let p := hamiltonianCoordinateMinorPolynomial (bipartiteLift T) a
  let D := fun t : Real => Matrix.det (hamiltonianParityRegularizedKernel T q t)
  let A := fun t : Real => (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
    Ring.inverse (hamiltonianParityRegularizedKernel T q t)
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let K := hamiltonianRepairKernel T q
  let S := hamiltonianParityProjection (Iota := Iota) q
  have hf := hamiltonian_polynomial_reverse_hasDerivAt p
  have hD := stochastic_regularized_determinant_hasDerivAt T q rho hq hRow hCol hNorm hRho
  have hA := stochastic_regularized_covariance_hasDerivAt T q rho hq hRow hCol hNorm hRho
  have hEntry := hamiltonian_matrix_entry_hasDerivAt A (K ^ 2 - K + S) hA a a
  have hDen : Filter.Eventually (fun t : Real => 0 < 1 + t) (nhds 0) := by
    exact (continuousAt_const.add continuousAt_id).eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (0 : Real) < 1 + 0))
  have hUnit := stochastic_regularized_root_unit_neighborhood T q rho hq hRow hCol hNorm hRho
  have hNear : Filter.Eventually (fun t : Real => Not (t = 0) ->
      Polynomial.eval (1 - t) p =
        D t * (t / (1 + t) * A t a a - S a a / (1 + t) ^ 2)) (nhds 0) := by
    filter_upwards [hDen, hUnit] with t hPos hU
    intro hNonzero
    exact stochastic_coordinate_minor_polynomial_cleared T q t hq hRow hCol
      hNonzero (ne_of_gt hPos) hU a
  have hJet := hamiltonian_cleared_root_derivative
    (fun t : Real => Polynomial.eval (1 - t) p) D (fun t : Real => A t a a)
    (fun _ : Real => S a a) (-Polynomial.eval 1 p.derivative)
    (D 0 * (1 / 2 - Matrix.trace G)) ((K ^ 2 - K + S) a a) 0
    hf hD hEntry (hasDerivAt_const (0 : Real) (S a a)) hNear
  have hDet := stochastic_regularized_root_determinant T q hq hRow hCol
  change -Polynomial.eval 1 p.derivative =
    D 0 * (A 0 a a + 2 * S a a - 0) -
      (D 0 * (1 / 2 - Matrix.trace G)) * S a a at hJet
  change D 0 = _ at hDet
  rw [hDet] at hJet
  change -(1 / 2 : Real) * Polynomial.eval 1 (polynomialEuler p) = _
  simp only [polynomialEuler, Polynomial.eval_mul, Polynomial.eval_X, one_mul]
  nlinarith only [hJet]

theorem stochastic_coordinate_pair_minor_moment_root
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) (a b : Sum Iota Iota) (hAB : Not (a = b)) :
    let d := Matrix.det ((1 : Matrix Iota Iota Real) -
      (centeredKernel T q).transpose * centeredKernel T q)
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
      Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
    let Aprime := (hamiltonianRepairKernel T q) ^ 2 -
      hamiltonianRepairKernel T q + hamiltonianParityProjection q
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    hamiltonianCoordinatePairMinorMoment (bipartiteLift T) a b =
      d * (A a a * A b b - A a b * A b a -
        hamiltonianParityCrossForm q Aprime a b +
        (3 / 2 + Matrix.trace G) * hamiltonianParityCrossForm q A a b) := by
  let p := hamiltonianCoordinatePairMinorPolynomial (bipartiteLift T) a b
  let D := fun t : Real => Matrix.det (hamiltonianParityRegularizedKernel T q t)
  let A := fun t : Real => (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
    Ring.inverse (hamiltonianParityRegularizedKernel T q t)
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let K := hamiltonianRepairKernel T q
  let S := hamiltonianParityProjection (Iota := Iota) q
  let Aprime := K ^ 2 - K + S
  have hf := hamiltonian_polynomial_reverse_hasDerivAt p
  have hD := stochastic_regularized_determinant_hasDerivAt T q rho hq hRow hCol hNorm hRho
  have hA := stochastic_regularized_covariance_hasDerivAt T q rho hq hRow hCol hNorm hRho
  have hEntry (i j : Sum Iota Iota) :=
    hamiltonian_matrix_entry_hasDerivAt A Aprime hA i j
  have hVRaw := ((hEntry a a).mul (hEntry b b)).sub ((hEntry a b).mul (hEntry b a))
  have hV : HasDerivAt
      (fun t : Real => A t a a * A t b b - A t a b * A t b a)
      (Aprime a a * A 0 b b + A 0 a a * Aprime b b -
        (Aprime a b * A 0 b a + A 0 a b * Aprime b a)) 0 := by
    simpa only [Pi.sub_apply, Pi.mul_apply] using! hVRaw
  have hcRaw := ((((hEntry b b).const_mul (S a a)).add
    ((hEntry a a).const_mul (S b b))).sub
      ((hEntry b a).const_mul (S a b))).sub
        ((hEntry a b).const_mul (S b a))
  have hc : HasDerivAt (fun t : Real => hamiltonianParityCrossForm q (A t) a b)
      (hamiltonianParityCrossForm q Aprime a b) 0 := by
    simpa only [hamiltonianParityCrossForm, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply] using! hcRaw
  have hDen : Filter.Eventually (fun t : Real => 0 < 1 + t) (nhds 0) := by
    exact (continuousAt_const.add continuousAt_id).eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (0 : Real) < 1 + 0))
  have hUnit := stochastic_regularized_root_unit_neighborhood T q rho hq hRow hCol hNorm hRho
  have hNear : Filter.Eventually (fun t : Real => Not (t = 0) ->
      Polynomial.eval (1 - t) p =
        D t * (t / (1 + t) * (A t a a * A t b b - A t a b * A t b a) -
          hamiltonianParityCrossForm q (A t) a b / (1 + t) ^ 2)) (nhds 0) := by
    filter_upwards [hDen, hUnit] with t hPos hU
    intro hNonzero
    exact stochastic_coordinate_pair_minor_polynomial_cleared T q t hq hRow hCol
      hNonzero (ne_of_gt hPos) hU a b hAB
  have hJet := hamiltonian_cleared_root_derivative
    (fun t : Real => Polynomial.eval (1 - t) p) D
    (fun t : Real => A t a a * A t b b - A t a b * A t b a)
    (fun t : Real => hamiltonianParityCrossForm q (A t) a b)
    (-Polynomial.eval 1 p.derivative) (D 0 * (1 / 2 - Matrix.trace G))
    _ (hamiltonianParityCrossForm q Aprime a b) hf hD hV hc hNear
  have hDet := stochastic_regularized_root_determinant T q hq hRow hCol
  change D 0 = _ at hDet
  rw [hDet] at hJet
  change -(1 / 2 : Real) * Polynomial.eval 1 (polynomialEuler p) = _
  simp only [polynomialEuler, Polynomial.eval_mul, Polynomial.eval_X, one_mul]
  nlinarith only [hJet]

end PrimeFactorOscillations
