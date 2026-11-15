/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection
import PrimeFactorOscillations.Helpers.HamiltonianTraceSupportCompensation

/-! # Joint stability of the full signed first covariance correction

Every diagonal, triple and cubic term is retained before subtraction.
The error estimates apply to these exact differences and to the disjoint
removed support, including the removed-by-removed overlap once.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

noncomputable section

namespace PrimeFactorOscillations

private theorem threeFactorBound
    (a b d A B C : Real) (hA0 : 0 <= A) (hB0 : 0 <= B)
    (hA : abs a <= A) (hB : abs b <= B) (hC : abs d <= C) :
    abs (a * b * d) <= A * B * C := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hA hB (abs_nonneg b) hA0) hC
    (abs_nonneg d) (mul_nonneg hA0 hB0)

private theorem squareDifferenceBound (a b c eps : Real) (hc : 0 <= c)
    (hEps : 0 <= eps) (ha : abs a <= c) (hb : abs b <= c)
    (hDiff : abs (a - b) <= eps) :
    abs (a ^ 2 - b ^ 2) <= 2 * c * eps := by
  have hEq : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have hSum : abs (a + b) <= 2 * c := by
    have h := abs_add_le a b
    linarith only [h, ha, hb]
  rw [hEq, abs_mul]
  have h := mul_le_mul hDiff hSum (abs_nonneg (a + b)) hEps
  nlinarith only [h]

private theorem tripleDifferenceBound (a b d x y z c eps : Real)
    (hc : 0 <= c) (hEps : 0 <= eps)
    (ha : abs a <= c) (hb : abs b <= c) (hd : abs d <= c)
    (hx : abs x <= c) (hy : abs y <= c) (hz : abs z <= c)
    (hax : abs (a - x) <= eps) (hby : abs (b - y) <= eps)
    (hdz : abs (d - z) <= eps) :
    abs (a * b * d - x * y * z) <= 3 * c ^ 2 * eps := by
  have hOne : abs ((a - x) * b * d) <= c ^ 2 * eps := by
    have h := threeFactorBound (a - x) b d eps c c hEps hc hax hb hd
    nlinarith only [h]
  have hTwo : abs (x * (b - y) * d) <= c ^ 2 * eps := by
    have h := threeFactorBound x (b - y) d c eps c hc hEps hx hby hd
    nlinarith only [h]
  have hThree : abs (x * y * (d - z)) <= c ^ 2 * eps :=
    by
      have h := threeFactorBound x y (d - z) c c eps hc hc hx hy hdz
      nlinarith only [h]
  have hEq : a * b * d - x * y * z =
      (a - x) * b * d + x * (b - y) * d + x * y * (d - z) := by ring
  rw [hEq]
  have hT1 := abs_add_le ((a - x) * b * d + x * (b - y) * d) (x * y * (d - z))
  have hT2 := abs_add_le ((a - x) * b * d) (x * (b - y) * d)
  nlinarith only [hT1, hT2, hOne, hTwo, hThree]

private theorem correctionDifferenceAssembly (d t u : Real)
    (hD : 0 <= d) (hT : 0 <= t)
    (D1 D0 T1 T0 U1 U0 : Real)
    (hDiag : abs (D1 - D0) <= d)
    (hTriple : abs (T1 - T0) <= t) (hCubic : abs (U1 - U0) <= u) :
    abs ((-(3 / 4 : Real) * D1 + (1 / 2 : Real) * T1 + (1 / 3 : Real) * U1) -
      (-(3 / 4 : Real) * D0 + (1 / 2 : Real) * T0 + (1 / 3 : Real) * U0)) <=
        d + t / 2 + u / 3 := by
  have hEq :
      (-(3 / 4 : Real) * D1 + (1 / 2 : Real) * T1 + (1 / 3 : Real) * U1) -
      (-(3 / 4 : Real) * D0 + (1 / 2 : Real) * T0 + (1 / 3 : Real) * U0) =
      -(3 / 4 : Real) * (D1 - D0) + (1 / 2 : Real) * (T1 - T0) +
        (1 / 3 : Real) * (U1 - U0) := by ring
  rw [hEq]
  have hA := abs_add_le (-(3 / 4 : Real) * (D1 - D0) + (1 / 2 : Real) * (T1 - T0))
    ((1 / 3 : Real) * (U1 - U0))
  have hB := abs_add_le (-(3 / 4 : Real) * (D1 - D0)) ((1 / 2 : Real) * (T1 - T0))
  have hAbsD : abs (-(3 / 4 : Real) * (D1 - D0)) = (3 / 4 : Real) * abs (D1 - D0) := by
    rw [abs_mul, abs_of_nonpos (by norm_num : -(3 / 4 : Real) <= 0)]
    ring
  have hAbsT : abs ((1 / 2 : Real) * (T1 - T0)) = (1 / 2 : Real) * abs (T1 - T0) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
  have hAbsU : abs ((1 / 3 : Real) * (U1 - U0)) = (1 / 3 : Real) * abs (U1 - U0) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 3)]
  nlinarith only [hA, hB, hAbsD, hAbsT, hAbsU, hDiag, hTriple, hCubic, hD]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem covarianceCorrection_entry_difference_bound
    (M N : Matrix Iota Iota Real) (c eps : Real) (hc : 0 <= c) (hEps : 0 <= eps)
    (hM : forall i j, abs (M i j) <= c) (hN : forall i j, abs (N i j) <= c)
    (hDiff : forall i j, abs (N i j - M i j) <= eps) :
    abs (covarianceCorrection N - covarianceCorrection M) <=
      2 * (Fintype.card Iota : Real) * c * eps +
        3 * (Fintype.card Iota : Real) ^ 2 * c ^ 2 * eps := by
  let m : Real := Fintype.card Iota
  have hm : 0 <= m := Nat.cast_nonneg _
  have hDiag : abs (covarianceDiagonalEnergy N - covarianceDiagonalEnergy M) <=
      2 * m * c * eps := by
    unfold covarianceDiagonalEnergy
    rw [<- Finset.sum_sub_distrib]
    calc
      _ <= Finset.sum Finset.univ (fun i => abs (N i i ^ 2 - M i i ^ 2)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : Iota => 2 * c * eps) :=
        Finset.sum_le_sum (fun i _ =>
          squareDifferenceBound (N i i) (M i i) c eps hc hEps (hN i i) (hM i i) (hDiff i i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]; ring
  have hTriple : abs (covarianceTriple N - covarianceTriple M) <= 3 * m ^ 2 * c ^ 2 * eps := by
    have hEach (i j : Iota) :
        abs (N i i * N j j * N i j - M i i * M j j * M i j) <= 3 * c ^ 2 * eps :=
      tripleDifferenceBound _ _ _ _ _ _ c eps hc hEps
        (hN i i) (hN j j) (hN i j) (hM i i) (hM j j) (hM i j)
        (hDiff i i) (hDiff j j) (hDiff i j)
    have h := hamiltonian_rectangular_sum_entry_bound _ (3 * c ^ 2 * eps) hEach
    have hEq : covarianceTriple N - covarianceTriple M =
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => N i i * N j j * N i j - M i i * M j j * M i j)) := by
      simp only [covarianceTriple, Finset.sum_sub_distrib]
    rw [<- hEq] at h
    nlinarith only [h]
  have hCubic : abs (covarianceCubic N - covarianceCubic M) <= 3 * m ^ 2 * c ^ 2 * eps := by
    have hEach (i j : Iota) : abs (N i j ^ 3 - M i j ^ 3) <= 3 * c ^ 2 * eps := by
      have h := tripleDifferenceBound (N i j) (N i j) (N i j) (M i j) (M i j) (M i j)
        c eps hc hEps (hN i j) (hN i j) (hN i j) (hM i j) (hM i j) (hM i j)
          (hDiff i j) (hDiff i j) (hDiff i j)
      simpa only [pow_succ, pow_zero, one_mul] using h
    have h := hamiltonian_rectangular_sum_entry_bound _ (3 * c ^ 2 * eps) hEach
    have hEq : covarianceCubic N - covarianceCubic M =
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => N i j ^ 3 - M i j ^ 3)) := by
      simp only [covarianceCubic, Finset.sum_sub_distrib]
    rw [<- hEq] at h
    nlinarith only [h]
  have hD : 0 <= 2 * m * c * eps :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm) hc) hEps
  have hT : 0 <= 3 * m ^ 2 * c ^ 2 * eps :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg m)) (sq_nonneg c)) hEps
  have h := correctionDifferenceAssembly (2 * m * c * eps) (3 * m ^ 2 * c ^ 2 * eps)
    (3 * m ^ 2 * c ^ 2 * eps) hD hT
      (covarianceDiagonalEnergy N) (covarianceDiagonalEnergy M)
      (covarianceTriple N) (covarianceTriple M) (covarianceCubic N) (covarianceCubic M)
        hDiag hTriple hCubic
  change abs (covarianceCorrection N - covarianceCorrection M) <=
    2 * m * c * eps + 3 * m ^ 2 * c ^ 2 * eps
  unfold covarianceCorrection
  nlinarith only [h, hT]

theorem covarianceCorrection_restriction_bound
    (M : Matrix Iota Iota Real) (D : Finset Iota) (c : Real) (hc : 0 <= c)
    (hM : forall i j, abs (M i j) <= c) :
    let rr := fun i : (Compl.compl D : Finset Iota) => (i.val : Iota)
    abs (covarianceCorrection (M.submatrix rr rr) - covarianceCorrection M) <=
      (D.card : Real) * c ^ 2 + 2 * (D.card : Real) * (Fintype.card Iota : Real) * c ^ 3 := by
  let R : Finset Iota := Compl.compl D
  let rr := fun i : R => (i.val : Iota)
  let MR := M.submatrix rr rr
  let d : Real := D.card
  let m : Real := Fintype.card Iota
  have hd : 0 <= d := Nat.cast_nonneg _
  have hm : 0 <= m := Nat.cast_nonneg _
  have hSquare (i : Iota) : M i i ^ 2 <= c ^ 2 := by
    have h := mul_le_mul (hM i i) (hM i i) (abs_nonneg _) hc
    simpa only [<- pow_two, sq_abs] using h
  have hDeleted0 : 0 <= Finset.sum Finset.univ (fun i : D => M i.val i.val ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hDeleted : Finset.sum Finset.univ (fun i : D => M i.val i.val ^ 2) <= d * c ^ 2 := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => c ^ 2) :=
        Finset.sum_le_sum (fun i _ => hSquare i.val)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, d]
  have hPartition : covarianceDiagonalEnergy M = covarianceDiagonalEnergy MR +
      Finset.sum Finset.univ (fun i : D => M i.val i.val ^ 2) := by
    have h := hamiltonian_sum_support_partition (fun i => M i i ^ 2) D
    have hSwap := h.trans (add_comm _ _)
    simpa only [covarianceDiagonalEnergy, MR, Matrix.submatrix_apply, rr] using hSwap
  have hDiag : abs (covarianceDiagonalEnergy MR - covarianceDiagonalEnergy M) <= d * c ^ 2 := by
    have hEq : covarianceDiagonalEnergy MR - covarianceDiagonalEnergy M =
        -(Finset.sum Finset.univ (fun i : D => M i.val i.val ^ 2)) := by
      linarith only [hPartition]
    rw [hEq, abs_neg, abs_of_nonneg hDeleted0]
    exact hDeleted
  have hTriple : abs (covarianceTriple MR - covarianceTriple M) <= 2 * d * m * c ^ 3 := by
    let A : Matrix Iota Iota Real := fun i j => M i i * M j j * M i j
    let B : Matrix Iota Iota Real := fun _ _ => 1
    have hEach (i j : Iota) : abs (A i j * B j i) <= c ^ 3 := by
      have h := threeFactorBound (M i i) (M j j) (M i j) c c c hc hc
        (hM i i) (hM j j) (hM i j)
      change abs ((M i i * M j j * M i j) * 1) <= c ^ 3
      rw [mul_one]
      nlinarith only [h]
    have h := hamiltonian_trace_removed_pair_bound A B D (c ^ 3) (pow_nonneg hc 3) hEach
    have hRaw : abs (covarianceTriple M - covarianceTriple MR) <= 2 * d * m * c ^ 3 := by
      have hFull : Matrix.trace (A * B) = covarianceTriple M := by
        change Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => (M i i * M j j * M i j) * 1)) = covarianceTriple M
        simp only [mul_one, covarianceTriple]
      have hRet : Matrix.trace (A.submatrix rr rr * B.submatrix rr rr) = covarianceTriple MR := by
        change Finset.sum Finset.univ (fun i : R => Finset.sum Finset.univ
          (fun j : R => (M i.val i.val * M j.val j.val * M i.val j.val) * 1)) =
            covarianceTriple MR
        simp only [mul_one, covarianceTriple, MR, Matrix.submatrix_apply, rr]
      rw [hFull, hRet] at h
      exact h
    rw [abs_sub_comm]
    exact hRaw
  have hCubic : abs (covarianceCubic MR - covarianceCubic M) <= 2 * d * m * c ^ 3 := by
    let A : Matrix Iota Iota Real := fun i j => M i j ^ 3
    let B : Matrix Iota Iota Real := fun _ _ => 1
    have hEach (i j : Iota) : abs (A i j * B j i) <= c ^ 3 := by
      have h := threeFactorBound (M i j) (M i j) (M i j) c c c hc hc
        (hM i j) (hM i j) (hM i j)
      change abs (M i j ^ 3 * 1) <= c ^ 3
      rw [mul_one]
      simpa only [pow_succ, pow_zero, one_mul] using h
    have h := hamiltonian_trace_removed_pair_bound A B D (c ^ 3) (pow_nonneg hc 3) hEach
    have hRaw : abs (covarianceCubic M - covarianceCubic MR) <= 2 * d * m * c ^ 3 := by
      have hFull : Matrix.trace (A * B) = covarianceCubic M := by
        change Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => M i j ^ 3 * 1)) = covarianceCubic M
        simp only [mul_one, covarianceCubic]
      have hRet : Matrix.trace (A.submatrix rr rr * B.submatrix rr rr) = covarianceCubic MR := by
        change Finset.sum Finset.univ (fun i : R => Finset.sum Finset.univ
          (fun j : R => M i.val j.val ^ 3 * 1)) = covarianceCubic MR
        simp only [mul_one, covarianceCubic, MR, Matrix.submatrix_apply, rr]
      rw [hFull, hRet] at h
      exact h
    rw [abs_sub_comm]
    exact hRaw
  have hD : 0 <= d * c ^ 2 := mul_nonneg hd (sq_nonneg c)
  have hT : 0 <= 2 * d * m * c ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) hm) (pow_nonneg hc 3)
  have h := correctionDifferenceAssembly (d * c ^ 2) (2 * d * m * c ^ 3) (2 * d * m * c ^ 3)
    hD hT (covarianceDiagonalEnergy MR) (covarianceDiagonalEnergy M)
      (covarianceTriple MR) (covarianceTriple M) (covarianceCubic MR) (covarianceCubic M)
        hDiag hTriple hCubic
  change abs (covarianceCorrection MR - covarianceCorrection M) <= d * c ^ 2 + 2 * d * m * c ^ 3
  unfold covarianceCorrection
  nlinarith only [h, hT]

theorem covarianceCorrection_supported_difference_bound
    (M : Matrix Iota Iota Real) (D : Finset Iota)
    (N : Matrix (Compl.compl D : Finset Iota) (Compl.compl D : Finset Iota) Real)
    (c eps : Real) (hc : 0 <= c) (hEps : 0 <= eps)
    (hM : forall i j, abs (M i j) <= c)
    (hN : forall i j, abs (N i j) <= c)
    (hDiff : forall i j, abs (N i j - M i.val j.val) <= eps) :
    abs (covarianceCorrection N - covarianceCorrection M) <=
      2 * ((Compl.compl D : Finset Iota).card : Real) * c * eps +
        3 * ((Compl.compl D : Finset Iota).card : Real) ^ 2 * c ^ 2 * eps +
        (D.card : Real) * c ^ 2 + 2 * (D.card : Real) * (Fintype.card Iota : Real) * c ^ 3 := by
  let rr := fun i : (Compl.compl D : Finset Iota) => (i.val : Iota)
  have hRet : forall i j, abs (M.submatrix rr rr i j) <= c := fun i j => hM i.val j.val
  have hLocal := covarianceCorrection_entry_difference_bound (M.submatrix rr rr) N c eps
    hc hEps hRet hN hDiff
  have hRemoved := covarianceCorrection_restriction_bound M D c hc hM
  have hTriangle := abs_add_le (covarianceCorrection N - covarianceCorrection (M.submatrix rr rr))
    (covarianceCorrection (M.submatrix rr rr) - covarianceCorrection M)
  have hEq : covarianceCorrection N - covarianceCorrection (M.submatrix rr rr) +
      (covarianceCorrection (M.submatrix rr rr) - covarianceCorrection M) =
        covarianceCorrection N - covarianceCorrection M := by ring
  rw [hEq] at hTriangle
  simp only [Fintype.card_coe] at hLocal
  linarith only [hTriangle, hLocal, hRemoved]

end PrimeFactorOscillations
