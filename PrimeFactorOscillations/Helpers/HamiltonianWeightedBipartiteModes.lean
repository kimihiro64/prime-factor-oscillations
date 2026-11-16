/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteEigenvalues
import PrimeFactorOscillations.Helpers.HamiltonianHermitianDeflation

/-! # Weighted Perron modes and exact nontrivial spectral readout -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianWeightedCrossMode (u v : Iota -> Real) (R : Real) :
    Matrix Iota Iota Real := fun i j => u i * v j / R

def hamiltonianWeightedPlus (u v : Iota -> Real) : Sum Iota Iota -> Real :=
  Sum.elim u v

def hamiltonianWeightedMinus (u v : Iota -> Real) : Sum Iota Iota -> Real :=
  Sum.elim u (fun j => -v j)

theorem hamiltonian_weighted_mode_left (u v : Iota -> Real) (R : Real)
    (x : Sum Iota Iota -> Real) (i : Iota) :
    (bipartiteLift (hamiltonianWeightedCrossMode u v R)).mulVec x (Sum.inl i) =
      (u i / R) * Finset.univ.sum (fun j => v j * x (Sum.inr j)) := by
  rw [hamiltonian_bipartite_mulVec_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [hamiltonianWeightedCrossMode]
  ring

theorem hamiltonian_weighted_mode_right (u v : Iota -> Real) (R : Real)
    (x : Sum Iota Iota -> Real) (j : Iota) :
    (bipartiteLift (hamiltonianWeightedCrossMode u v R)).mulVec x (Sum.inr j) =
      (v j / R) * Finset.univ.sum (fun i => u i * x (Sum.inl i)) := by
  rw [hamiltonian_bipartite_mulVec_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [hamiltonianWeightedCrossMode]
  ring

theorem hamiltonian_weighted_mode_signed_actions
    (u v : Iota -> Real) (R : Real) (hR : Not (R = 0))
    (hU : Finset.univ.sum (fun i => u i ^ 2) = R)
    (hV : Finset.univ.sum (fun j => v j ^ 2) = R) :
    (forall i, (bipartiteLift (hamiltonianWeightedCrossMode u v R)).mulVec
      (hamiltonianWeightedPlus u v) i = hamiltonianWeightedPlus u v i) /\
    (forall i, (bipartiteLift (hamiltonianWeightedCrossMode u v R)).mulVec
      (hamiltonianWeightedMinus u v) i = -(hamiltonianWeightedMinus u v i)) := by
  have hU' : Finset.univ.sum (fun i => u i * u i) = R := by
    simpa only [pow_two] using hU
  have hV' : Finset.univ.sum (fun j => v j * v j) = R := by
    simpa only [pow_two] using hV
  have hVNeg : Finset.univ.sum (fun j => v j * (-v j)) = -R := by
    simp only [mul_neg, Finset.sum_neg_distrib, hV']
  constructor
  . intro s
    cases s with
    | inl i =>
      rw [hamiltonian_weighted_mode_left]
      change (u i / R) * Finset.univ.sum (fun j => v j * v j) = u i
      rw [hV']
      field_simp [hR]
    | inr j =>
      rw [hamiltonian_weighted_mode_right]
      change (v j / R) * Finset.univ.sum (fun i => u i * u i) = v j
      rw [hU']
      field_simp [hR]
  . intro s
    cases s with
    | inl i =>
      rw [hamiltonian_weighted_mode_left]
      change (u i / R) * Finset.univ.sum (fun j => v j * (-v j)) = -u i
      rw [hVNeg]
      field_simp [hR]
    | inr j =>
      rw [hamiltonian_weighted_mode_right]
      change (v j / R) * Finset.univ.sum (fun i => u i * u i) = -(-v j)
      rw [hU']
      field_simp [hR]
      <;> ring

theorem hamiltonian_weighted_eigenvector_sums
    (S : Matrix Iota Iota Real) (u v : Iota -> Real)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (x : Sum Iota Iota -> Real) (lambda : Real)
    (hEigen : forall i, (bipartiteLift S).mulVec x i = lambda * x i)
    (hOne : Not (lambda = 1)) (hMinus : Not (lambda = -(1 : Real))) :
    (Finset.univ.sum (fun i => u i * x (Sum.inl i)) = 0) /\
      (Finset.univ.sum (fun j => v j * x (Sum.inr j)) = 0) := by
  let su := Finset.univ.sum (fun i => u i * x (Sum.inl i))
  let sv := Finset.univ.sum (fun j => v j * x (Sum.inr j))
  have hR' (j : Iota) : Finset.univ.sum (fun i => u i * S i j) = v j := by
    simpa only [mul_comm] using hRight j
  have hL' (i : Iota) : Finset.univ.sum (fun j => v j * S i j) = u i := by
    simpa only [mul_comm] using hLeft i
  have hL : lambda * su = sv := by
    calc
      _ = Finset.univ.sum (fun i => u i * (lambda * x (Sum.inl i))) := by
        dsimp [su]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = Finset.univ.sum (fun i => u i * (bipartiteLift S).mulVec x (Sum.inl i)) :=
        Finset.sum_congr rfl (fun i _ => congrArg (fun a => u i * a) (hEigen (Sum.inl i)).symm)
      _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
          (u i * S i j) * x (Sum.inr j))) := by
        simp only [hamiltonian_bipartite_mulVec_left, Finset.mul_sum, mul_assoc]
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun i =>
          (u i * S i j) * x (Sum.inr j))) := Finset.sum_comm
      _ = sv := by simp only [<- Finset.sum_mul, hR', sv]
  have hR : lambda * sv = su := by
    calc
      _ = Finset.univ.sum (fun j => v j * (lambda * x (Sum.inr j))) := by
        dsimp [sv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = Finset.univ.sum (fun j => v j * (bipartiteLift S).mulVec x (Sum.inr j)) :=
        Finset.sum_congr rfl (fun j _ => congrArg (fun a => v j * a) (hEigen (Sum.inr j)).symm)
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun i =>
          (v j * S i j) * x (Sum.inl i))) := by
        simp only [hamiltonian_bipartite_mulVec_right, Finset.mul_sum, mul_assoc]
      _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
          (v j * S i j) * x (Sum.inl i))) := Finset.sum_comm
      _ = su := by simp only [<- Finset.sum_mul, hL', su]
  have hplus : (lambda - 1) * (su + sv) = 0 := by nlinarith only [hL, hR]
  have hminus : (lambda + 1) * (su - sv) = 0 := by nlinarith only [hL, hR]
  have hOne' : Not (lambda - 1 = 0) := by intro h; apply hOne; linarith only [h]
  have hMinus' : Not (lambda + 1 = 0) := by intro h; apply hMinus; linarith only [h]
  have hp : su + sv = 0 := (mul_eq_zero.mp hplus).resolve_left hOne'
  have hm : su - sv = 0 := (mul_eq_zero.mp hminus).resolve_left hMinus'
  constructor
  . change su = 0; linarith only [hp, hm]
  . change sv = 0; linarith only [hp, hm]

theorem hamiltonian_weighted_simple_spectral_gap
    (S : Matrix Iota Iota Real) (u v : Iota -> Real) (R rho : Real)
    (hR : Not (R = 0)) (hp : 0 <= rho)
    (hU : Finset.univ.sum (fun i => u i ^ 2) = R)
    (hV : Finset.univ.sum (fun j => v j ^ 2) = R)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (hSimplePlus : forall x : Sum Iota Iota -> Real,
      (forall i, (bipartiteLift S).mulVec x i = x i) ->
      exists a : Real, forall i, x i = a * hamiltonianWeightedPlus u v i)
    (hSimpleMinus : forall x : Sum Iota Iota -> Real,
      (forall i, (bipartiteLift S).mulVec x i = -x i) ->
      exists a : Real, forall i, x i = a * hamiltonianWeightedMinus u v i)
    (hSpectrum : forall k : Sum Iota Iota,
      Not ((bipartiteLift_hermitian S).eigenvalues k = 1) ->
      Not ((bipartiteLift_hermitian S).eigenvalues k = -(1 : Real)) ->
      abs ((bipartiteLift_hermitian S).eigenvalues k) <= rho) :
    norm (S - hamiltonianWeightedCrossMode u v R) <= rho := by
  let M := bipartiteLift S
  let P := bipartiteLift (hamiltonianWeightedCrossMode u v R)
  let U := realGaussianEigenMatrix M (bipartiteLift_hermitian S)
  let lam := (bipartiteLift_hermitian S).eigenvalues
  have hEigen (k i : Sum Iota Iota) :
      M.mulVec (fun j => U j k) i = lam k * U i k := by
    have h := congrArg (fun A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real => A i k)
      (hamiltonian_real_eigenmatrix_action M (bipartiteLift_hermitian S))
    change (M * U) i k = (U * Matrix.diagonal lam) i k at h
    rw [Matrix.mul_diagonal] at h
    change Finset.univ.sum (fun j => M i j * U j k) = U i k * lam k at h
    change Finset.univ.sum (fun j => M i j * U j k) = lam k * U i k
    exact h.trans (mul_comm _ _)
  have hActions := hamiltonian_weighted_mode_signed_actions u v R hR hU hV
  have hExceptional : forall k, Or (lam k = 1) (lam k = -(1 : Real)) ->
      forall i, (P * U) i k = U i k * lam k := by
    intro k he i
    cases he with
    | inl he =>
      have hOne : forall s, M.mulVec (fun j => U j k) s = U s k := by
        intro s; simpa only [he, one_mul] using hEigen k s
      choose a ha using hSimplePlus (fun j => U j k) hOne
      change Finset.univ.sum (fun j => P i j * U j k) = U i k * lam k
      simp_rw [ha]
      rw [he, mul_one]
      have hAct := hActions.1 i
      change Finset.univ.sum (fun j => P i j * hamiltonianWeightedPlus u v j) =
        hamiltonianWeightedPlus u v i at hAct
      calc
        _ = a * Finset.univ.sum (fun j => P i j * hamiltonianWeightedPlus u v j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [hAct]
    | inr he =>
      have hNeg : forall s, M.mulVec (fun j => U j k) s = -U s k := by
        intro s; simpa only [he, neg_one_mul] using hEigen k s
      choose a ha using hSimpleMinus (fun j => U j k) hNeg
      change Finset.univ.sum (fun j => P i j * U j k) = U i k * lam k
      simp_rw [ha]
      rw [he]
      have hAct := hActions.2 i
      change Finset.univ.sum (fun j => P i j * hamiltonianWeightedMinus u v j) =
        -(hamiltonianWeightedMinus u v i) at hAct
      calc
        _ = a * Finset.univ.sum (fun j => P i j * hamiltonianWeightedMinus u v j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [hAct]; ring
  have hOther : forall k, Not (lam k = 1) -> Not (lam k = -(1 : Real)) ->
      forall i, (P * U) i k = 0 := by
    intro k hp1 hpm i
    have hSums := hamiltonian_weighted_eigenvector_sums S u v hLeft hRight
      (fun j => U j k) (lam k) (hEigen k) hp1 hpm
    change P.mulVec (fun j => U j k) i = 0
    cases i with
    | inl i =>
      rw [hamiltonian_weighted_mode_left, hSums.2, mul_zero]
    | inr j =>
      rw [hamiltonian_weighted_mode_right, hSums.1, mul_zero]
  have hFull := hamiltonian_hermitian_signed_deflation_norm M
    (bipartiteLift_hermitian S) P rho hp hSpectrum hExceptional hOther
  have hDiff : M - P = bipartiteLift (S - hamiltonianWeightedCrossMode u v R) := by
    ext i j
    cases i <;> cases j <;>
      simp [M, P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose, Matrix.sub_apply]
  rw [hDiff, hamiltonian_bipartite_lift_norm] at hFull
  exact hFull

end PrimeFactorOscillations
