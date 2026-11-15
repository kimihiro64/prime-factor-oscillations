/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAffineSpectralJet
import PrimeFactorOscillations.Helpers.HamiltonianResolventSpectralTrace

/-! # The actual determinant second derivative in full covariance traces

The matrix is diagonalized before differentiating its positive local
determinant factor. Signed eigenvalues and every cross-block product
in the trace of the covariance square are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hermitianDeterminantFactor (M : Matrix Iota Iota Real) (t : Real) : Real :=
  Real.rpow (Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M))
    (-(1 / 2 : Real))

theorem hermitianDeterminantFactor_eq_affine (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (t : Real) (hPos : forall i, 0 < 1 + t * hM.eigenvalues i) :
    hermitianDeterminantFactor M t = affineSpectralFactors Finset.univ hM.eigenvalues t := by
  have hDet : Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M) =
      Finset.prod Finset.univ (fun i => 1 + t * hM.eigenvalues i) := by
    simpa only [neg_smul, sub_neg_eq_add, neg_mul] using
      hermitian_det_one_sub_smul M hM (-t)
  have hProd : 0 < Finset.prod Finset.univ (fun i => 1 + t * hM.eigenvalues i) :=
    Finset.prod_pos (fun i _ => hPos i)
  unfold hermitianDeterminantFactor
  rw [hDet]
  change (Finset.prod Finset.univ (fun i => 1 + t * hM.eigenvalues i)) ^
    (-(1 / 2 : Real)) = _
  rw [Real.rpow_def_of_pos hProd]
  unfold affineSpectralFactors affineSpectralCoordinate0
  congr 1
  rw [Real.log_prod (fun i _ => ne_of_gt (hPos i)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hermitianDeterminantFactor_eventually_eq_affine (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (t : Real) (hPos : forall i, 0 < 1 + t * hM.eigenvalues i) :
    Filter.EventuallyEq (nhds t) (hermitianDeterminantFactor M)
      (affineSpectralFactors Finset.univ hM.eigenvalues) := by
  have hEach (i : Iota) : Filter.Eventually
      (fun s : Real => 0 < 1 + s * hM.eigenvalues i) (nhds t) := by
    have hContinuous : ContinuousAt (fun s : Real => 1 + s * hM.eigenvalues i) t :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    exact hContinuous.eventually (isOpen_Ioi.mem_nhds (hPos i))
  have hAll := (Filter.eventually_all_finset (Finset.univ : Finset Iota)).mpr
    (fun i _ => hEach i)
  exact hAll.mono (fun s hs =>
    hermitianDeterminantFactor_eq_affine M hM s (fun i => hs i (Finset.mem_univ i)))

theorem hermitianDeterminantFactor_pos (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (t : Real) (hPos : forall i, 0 < 1 + t * hM.eigenvalues i) :
    0 < hermitianDeterminantFactor M t := by
  rw [hermitianDeterminantFactor_eq_affine M hM t hPos]
  exact Real.exp_pos _

theorem hermitianDeterminantFactor_covariance_second_derivative
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (hPos : forall i, 0 < 1 + hM.eigenvalues i) :
    deriv (deriv (hermitianDeterminantFactor M)) 1 =
      hermitianDeterminantFactor M 1 *
        ((Matrix.trace (resolventCovariance M)) ^ 2 / 4 +
          Matrix.trace (resolventCovariance M * resolventCovariance M) / 2) := by
  have hPosAt (i : Iota) : 0 < 1 + (1 : Real) * hM.eigenvalues i := by
    simpa only [one_mul] using hPos i
  have hDen (i : Iota) : Not (1 + hM.eigenvalues i = 0) := ne_of_gt (hPos i)
  have hDenAt (i : Iota) (_hi : Membership.mem (Finset.univ : Finset Iota) i) :
      Not (1 + (1 : Real) * hM.eigenvalues i = 0) := by
    simpa only [one_mul] using hDen i
  have hTraceData := hermitian_resolvent_spectral_traces M hM hDen
  have hFirst :
      Finset.sum Finset.univ (fun i => affineSpectralCoordinate1 (hM.eigenvalues i) 1) =
        -(1 / 2 : Real) * Matrix.trace (resolventCovariance M) := by
    rw [hTraceData.2.1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [affineSpectralCoordinate1, one_mul]
    ring
  have hSecond :
      Finset.sum Finset.univ (fun i => affineSpectralCoordinate2 (hM.eigenvalues i) 1) =
        (1 / 2 : Real) * Matrix.trace (resolventCovariance M * resolventCovariance M) := by
    rw [hTraceData.2.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [affineSpectralCoordinate2, one_mul, div_pow]
    ring
  have hEq := hermitianDeterminantFactor_eventually_eq_affine M hM 1 hPosAt
  have hD2 := Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.deriv hEq)
  have hValue := hermitianDeterminantFactor_eq_affine M hM 1 hPosAt
  calc
    _ = deriv (deriv (affineSpectralFactors Finset.univ hM.eigenvalues)) 1 := hD2
    _ = affineSpectralFactors Finset.univ hM.eigenvalues 1 *
        ((Finset.sum Finset.univ (fun i => affineSpectralCoordinate1 (hM.eigenvalues i) 1)) ^ 2 +
          Finset.sum Finset.univ (fun i => affineSpectralCoordinate2 (hM.eigenvalues i) 1)) :=
      affineSpectralFactors_second_derivative Finset.univ hM.eigenvalues 1 hDenAt
    _ = _ := by rw [<- hValue, hFirst, hSecond]; ring

end PrimeFactorOscillations
