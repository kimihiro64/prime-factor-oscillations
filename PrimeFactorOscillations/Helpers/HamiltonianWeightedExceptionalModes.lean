/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianInverseDegreeNormalization

/-! # Simplicity of both weighted Perron modes from the actual norm defect -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_weighted_eigenvector_coupling
    (S : Matrix Iota Iota Real) (u v : Iota -> Real)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (x : Sum Iota Iota -> Real) (lambda : Real)
    (hEigen : forall i, (bipartiteLift S).mulVec x i = lambda * x i) :
    (lambda * Finset.univ.sum (fun i => u i * x (Sum.inl i)) =
        Finset.univ.sum (fun j => v j * x (Sum.inr j))) /\
      (lambda * Finset.univ.sum (fun j => v j * x (Sum.inr j)) =
        Finset.univ.sum (fun i => u i * x (Sum.inl i))) := by
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
  exact And.intro hL hR

theorem hamiltonian_weighted_exceptional_mode_simple
    (S : Matrix Iota Iota Real) (u v : Iota -> Real) (R rho sigma : Real)
    (hR : Not (R = 0)) (hRho : rho < 1)
    (hU : Finset.univ.sum (fun i => u i ^ 2) = R)
    (hV : Finset.univ.sum (fun j => v j ^ 2) = R)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (hSign : sigma = 1 \/ sigma = -(1 : Real))
    (hNorm : norm (S - hamiltonianWeightedCrossMode u v R) <= rho)
    (x : Sum Iota Iota -> Real)
    (hEigen : forall i, (bipartiteLift S).mulVec x i = sigma * x i) :
    exists a : Real, forall i,
      x i = a * Sum.elim u (fun j => sigma * v j) i := by
  let w := Sum.elim u (fun j => sigma * v j)
  let su := Finset.univ.sum (fun i => u i * x (Sum.inl i))
  let sv := Finset.univ.sum (fun j => v j * x (Sum.inr j))
  let a := su / R
  let y := fun i => x i - a * w i
  let M := bipartiteLift S
  let P := bipartiteLift (hamiltonianWeightedCrossMode u v R)
  have hSigmaSquare : sigma * sigma = 1 := by
    cases hSign with
    | inl he => rw [he]; norm_num
    | inr he => rw [he]; norm_num
  have hMode (i : Sum Iota Iota) : M.mulVec w i = sigma * w i := by
    cases i with
    | inl i =>
      rw [hamiltonian_bipartite_mulVec_left]
      change Finset.univ.sum (fun j => S i j * (sigma * v j)) = sigma * u i
      calc
        _ = sigma * Finset.univ.sum (fun j => S i j * v j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = _ := by rw [hLeft]
    | inr j =>
      rw [hamiltonian_bipartite_mulVec_right]
      change Finset.univ.sum (fun i => S i j * u i) = sigma * (sigma * v j)
      rw [hRight, <- mul_assoc, hSigmaSquare, one_mul]
  have hCoupling := (hamiltonian_weighted_eigenvector_coupling
    S u v hLeft hRight x sigma hEigen).1
  change sigma * su = sv at hCoupling
  have hWR : Finset.univ.sum (fun i => u i * w (Sum.inl i)) = R := by
    simpa only [w, Sum.elim_inl, pow_two] using hU
  have hWV : Finset.univ.sum (fun j => v j * w (Sum.inr j)) = sigma * R := by
    calc
      _ = sigma * Finset.univ.sum (fun j => v j ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [w]
        ring
      _ = _ := by rw [hV]
  have hSubtract (f g z : Iota -> Real) :
      Finset.univ.sum (fun i => f i * (g i - a * z i)) =
        Finset.univ.sum (fun i => f i * g i) -
          a * Finset.univ.sum (fun i => f i * z i) := by
    calc
      _ = Finset.univ.sum (fun i => f i * g i - a * (f i * z i)) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hYSums :
      (Finset.univ.sum (fun i => u i * y (Sum.inl i)) = 0) /\
        (Finset.univ.sum (fun j => v j * y (Sum.inr j)) = 0) := by
    constructor
    . change Finset.univ.sum (fun i => u i * (x (Sum.inl i) - a * w (Sum.inl i))) = 0
      rw [hSubtract, hWR]
      change su - (su / R) * R = 0
      field_simp [hR]
      <;> ring
    . change Finset.univ.sum (fun j => v j * (x (Sum.inr j) - a * w (Sum.inr j))) = 0
      rw [hSubtract, hWV]
      change sv - (su / R) * (sigma * R) = 0
      have hCancel : (su / R) * (sigma * R) = sigma * su := by
        field_simp [hR]
        <;> ring
      rw [hCancel, <- hCoupling]
      ring
  have hYEigen (i : Sum Iota Iota) : M.mulVec y i = sigma * y i := by
    have hScale : Finset.univ.sum (fun j => M i j * (a * w j)) =
        a * Finset.univ.sum (fun j => M i j * w j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    change Finset.univ.sum (fun j => M i j * (x j - a * w j)) = sigma * (x i - a * w i)
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hScale]
    change M.mulVec x i - a * M.mulVec w i = sigma * x i - sigma * (a * w i)
    rw [hEigen, hMode]
    ring
  have hReference (i : Sum Iota Iota) : P.mulVec y i = 0 := by
    cases i with
    | inl i => rw [hamiltonian_weighted_mode_left, hYSums.2, mul_zero]
    | inr j => rw [hamiltonian_weighted_mode_right, hYSums.1, mul_zero]
  have hDiff : M - P = bipartiteLift (S - hamiltonianWeightedCrossMode u v R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [M, P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose, Matrix.sub_apply]
  have hFull : norm (M - P) <= rho := by
    rw [hDiff, hamiltonian_bipartite_lift_norm]
    exact hNorm
  have hAbs : abs sigma = 1 := by
    cases hSign with
    | inl he => rw [he]; norm_num
    | inr he => rw [he]; norm_num
  have hZero (i : Sum Iota Iota) : y i = 0 := by
    by_contra hi
    have h := hamiltonian_eigenvalue_error_bound M P y sigma rho
      (Exists.intro i hi) hYEigen hReference hFull
    rw [hAbs] at h
    exact (not_lt_of_ge h) hRho
  refine Exists.intro a ?_
  intro i
  have h := hZero i
  change x i - a * w i = 0 at h
  linarith only [h]

theorem hamiltonian_actual_normalized_spectral_packet_from_raw [Nonempty Iota]
    (T : Matrix Iota Iota Real) (q eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hp0 : 0 <= rho) (hp1 : rho <= 1) (hMargin : rho + 16 * eps < 1)
    (hr : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hc : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hNorm : norm (centeredKernel T q) <= rho) :
    HamiltonianNormalizedSpectralPacket T (rho + 16 * eps) := by
  have hrPos (i : Iota) : 0 < hamiltonianCrossRowDegrees T i := by
    linarith only [(abs_le.mp (hr i)).1, he1]
  have hcPos (j : Iota) : 0 < hamiltonianCrossColumnDegrees T j := by
    linarith only [(abs_le.mp (hc j)).1, he1]
  have hR := ne_of_gt (hamiltonian_total_degree_positive T hrPos)
  have hNorms := hamiltonian_degree_roots_equal_norms T hrPos hcPos
  have hLeft := hamiltonian_actual_normalized_perron_left T hrPos hcPos
  have hRight := hamiltonian_actual_normalized_perron_right T hrPos hcPos
  have hGap := hamiltonian_actual_raw_to_normalized_degree_gap
    T q eps rho hq he0 he1 hp0 hp1 hr hc hNorm
  rw [hamiltonian_actual_normalized_mode_identity T q hq hrPos] at hGap
  constructor
  . intro x hx
    have hEigen (i : Sum Iota Iota) :
        (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i = 1 * x i := by
      simpa only [one_mul] using hx i
    simpa only [one_mul, hamiltonianWeightedPlus] using
      hamiltonian_weighted_exceptional_mode_simple
        (hamiltonianActualDegreeNormalizedCross T)
        (hamiltonianRowRoot T) (hamiltonianColumnRoot T)
        (hamiltonianTotalDegree T) (rho + 16 * eps) 1 hR hMargin
        hNorms.1 hNorms.2 hLeft hRight (Or.inl rfl) hGap x hEigen
  . intro x hx
    have hEigen (i : Sum Iota Iota) :
        (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i =
          -(1 : Real) * x i := by
      simpa only [neg_one_mul] using hx i
    simpa only [neg_one_mul, hamiltonianWeightedMinus] using
      hamiltonian_weighted_exceptional_mode_simple
        (hamiltonianActualDegreeNormalizedCross T)
        (hamiltonianRowRoot T) (hamiltonianColumnRoot T)
        (hamiltonianTotalDegree T) (rho + 16 * eps) (-1) hR hMargin
        hNorms.1 hNorms.2 hLeft hRight (Or.inr rfl) hGap x hEigen
  . intro k hOne hMinus
    exact hamiltonian_actual_normalized_native_readout
      T q eps rho hq he0 he1 hp0 hp1 hr hc hNorm k hOne hMinus

end PrimeFactorOscillations
