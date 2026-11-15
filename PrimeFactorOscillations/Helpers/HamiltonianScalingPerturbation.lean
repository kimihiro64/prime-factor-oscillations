/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStochasticScalingCost

/-! # Full scaling and rank-centering perturbations

The complete linear, quadratic and centering terms are isolated exactly.
The actual entry budget is used only by the higher determinant remainder;
it is not a substitute for the signed linear trace.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianScalingPerturbation (P C : Matrix Iota Iota Real)
    (z : Iota -> Real) (q qNew : Real) : Matrix Iota Iota Real :=
  Matrix.diagonal (1 + z) * P * Matrix.diagonal (1 + z) - P + HSMul.hSMul (q - qNew) C

theorem hamiltonianScalingPerturbation_entry (P C : Matrix Iota Iota Real)
    (z : Iota -> Real) (q qNew : Real) (i j : Iota) :
    hamiltonianScalingPerturbation P C z q qNew i j =
      (z i + z j + z i * z j) * P i j + (q - qNew) * C i j := by
  simp only [hamiltonianScalingPerturbation, Matrix.add_apply, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.add_apply, Pi.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem hamiltonianScalingPerturbation_decomposition (P C : Matrix Iota Iota Real)
    (z : Iota -> Real) (q qNew : Real) :
    hamiltonianScalingPerturbation P C z q qNew =
      Matrix.diagonal z * P + P * Matrix.diagonal z +
        Matrix.diagonal z * P * Matrix.diagonal z + HSMul.hSMul (q - qNew) C := by
  apply Matrix.ext
  intro i j
  rw [hamiltonianScalingPerturbation_entry]
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem hamiltonianScalingPerturbation_entry_bound
    (P C : Matrix Iota Iota Real) (z : Iota -> Real) (q qNew b c : Real)
    (hb : 0 <= b) (_hc : 0 <= c)
    (hZ : forall i, abs (z i) <= b)
    (hP : forall i j, abs (P i j) <= c)
    (hC : forall i j, abs (C i j) <= 1) (i j : Iota) :
    abs (hamiltonianScalingPerturbation P C z q qNew i j) <=
      (2 * b + b ^ 2) * c + abs (q - qNew) := by
  have hCoefficient : abs (z i + z j + z i * z j) <= 2 * b + b ^ 2 := by
    have hMul := mul_le_mul (hZ i) (hZ j) (abs_nonneg _) hb
    calc
      _ <= abs (z i + z j) + abs (z i * z j) := abs_add_le _ _
      _ <= (abs (z i) + abs (z j)) + abs (z i) * abs (z j) := by
        rw [abs_mul]
        exact add_le_add (abs_add_le _ _) (le_refl _)
      _ <= _ := by nlinarith only [hZ i, hZ j, hMul]
  rw [hamiltonianScalingPerturbation_entry]
  calc
    _ <= abs ((z i + z j + z i * z j) * P i j) +
        abs ((q - qNew) * C i j) := abs_add_le _ _
    _ = abs (z i + z j + z i * z j) * abs (P i j) +
        abs (q - qNew) * abs (C i j) := by rw [abs_mul, abs_mul]
    _ <= (2 * b + b ^ 2) * c + abs (q - qNew) := by
      apply add_le_add
      exact mul_le_mul hCoefficient (hP i j) (abs_nonneg _) (by positivity)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hC i j) (abs_nonneg (q - qNew))

theorem hamiltonian_rank_shift_reference
    (N : Nat) (r q : Real) (hNq : (N : Real) * q = 1)
    (hr : 0 <= r) (hq : 0 <= q) (hSmall : r * q <= 1 / 2) :
    0 <= q / (1 - r * q) /\
    ((N : Real) - r) * (q / (1 - r * q)) = 1 /\
    abs (q - q / (1 - r * q)) <= 2 * r * q ^ 2 := by
  let d := 1 - r * q
  have hd : 0 < d := by dsimp only [d]; linarith only [hSmall]
  have hdHalf : 1 / 2 <= d := by dsimp only [d]; linarith only [hSmall]
  have hDen : Not (d = 0) := ne_of_gt hd
  have hDiff : q / d - q = r * q ^ 2 / d := by
    field_simp [hDen] <;> dsimp only [d] <;> ring
  have hPos : 0 <= r * q ^ 2 / d := div_nonneg (mul_nonneg hr (sq_nonneg q)) (le_of_lt hd)
  have hAbs : abs (q - q / d) = r * q ^ 2 / d := by
    rw [abs_sub_comm, hDiff, abs_of_nonneg hPos]
  have hClear : d * (r * q ^ 2 / d) = r * q ^ 2 := by field_simp
  have hBound : abs (q - q / d) <= 2 * r * q ^ 2 := by
    rw [hAbs]
    have h := mul_le_mul_of_nonneg_right hdHalf hPos
    nlinarith only [h, hClear]
  have hNorm : ((N : Real) - r) * (q / d) = 1 := by
    have hOne : ((N : Real) - r) * q = d := by dsimp only [d]; nlinarith only [hNq]
    rw [<- mul_div_assoc, hOne, div_self hDen]
  exact And.intro (div_nonneg hq (le_of_lt hd)) (And.intro hNorm hBound)

def hamiltonianRetainedCrossMask (S U : Finset Iota) :
    Matrix (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota))
      (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) Real :=
  (bipartiteLift (fun _ _ : Iota => (1 : Real))).submatrix
    (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val)
    (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val)

theorem hamiltonian_retained_centered_kernel
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (q : Real) :
    (bipartiteLift (centeredKernel T q)).submatrix
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val)
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val) =
      hamiltonianRetainedKernel T S U - HSMul.hSMul q (hamiltonianRetainedCrossMask S U) := by
  apply Matrix.ext
  intro i j
  cases hi : i.val <;> cases hj : j.val <;>
    simp [hamiltonianRetainedKernel, hamiltonianRetainedCrossMask, bipartiteLift,
      Matrix.fromBlocks, Matrix.transpose_apply, Matrix.transpose, centeredKernel, averagingKernel, hi, hj]

variable [Nonempty Iota]

theorem stochastic_scaling_centering_perturbation_entry
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hRho0 : 0 <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho)) :
    let r : Real := U.card
    let qNew := q / (1 - r * q)
    0 <= qNew /\
    ((Fintype.card Iota : Real) - r) * qNew = 1 /\
    forall i j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      abs (hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
        (hamiltonianRetainedCrossMask S U) z q qNew i j) <=
          44 * r * (a / (1 - rho)) ^ 2 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let P := hamiltonianRetainedKernel T S U
  let C := hamiltonianRetainedCrossMask S U
  let qNew := q / (1 - r * q)
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hr : 0 <= r := Nat.cast_nonneg _
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have ht : 0 <= t := by dsimp only [t]; positivity
  have hPt : p * t <= 1 / 1000 := by
    have hEq : p * t = r * a ^ 2 * q / delta ^ 2 := by dsimp only [p, t]; field_simp
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have hMul := mul_le_mul_of_nonneg_right hp ht
    nlinarith only [hMul, hPt]
  have hrq : r * q <= 1 / 2 := by
    have hMul := mul_le_mul_of_nonneg_right hp (mul_nonneg hr hq0)
    dsimp only [t] at htSmall
    nlinarith only [hMul, htSmall]
  have hRef := hamiltonian_rank_shift_reference (Fintype.card Iota) r q hq hr hq0 hrq
  have hAq : 0 <= a * q := mul_nonneg ha0 hq0
  have hAP : a * q <= p * q := by
    have h := mul_le_mul_of_nonneg_right hDelta1 hp0
    have hA : a <= p := by nlinarith only [h, hpClear]
    exact mul_le_mul_of_nonneg_right hA hq0
  have hPFull (i j : Sum Iota Iota) : abs (bipartiteLift T i j) <= a * q := by
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.transpose,
        abs_of_nonneg, hNonneg, hUpper, hAq]
  have hP (i j : R) : abs (P i j) <= a * q := hPFull i.val j.val
  have hCFull (i j : Sum Iota Iota) :
      abs (bipartiteLift (fun _ _ : Iota => (1 : Real)) i j) <= 1 := by
    cases i <;> cases j <;> norm_num [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.transpose]
  have hC (i j : R) : abs (C i j) <= 1 := hCFull i.val j.val
  have hZNorm : norm z <= 20 * t := by
    have hEq : 20 * r * a * q / (1 - rho) = 20 * t := by dsimp only [p, t, delta]; ring
    rw [hEq] at hZ
    exact hZ
  have hZPoint (i : R) : abs (z i) <= 20 * t := by
    have h := (pi_norm_le_iff_of_nonneg (by positivity)).mp hZNorm i
    simpa only [Real.norm_eq_abs] using h
  have hCoefficient : 2 * (20 * t) + (20 * t) ^ 2 <= 41 * t := by
    have h := mul_le_mul_of_nonneg_right htSmall ht
    nlinarith only [h]
  have hMain : (2 * (20 * t) + (20 * t) ^ 2) * (a * q) <= 41 * t * (p * q) :=
    mul_le_mul hCoefficient hAP hAq (by positivity)
  have hComplement : 2 * r * q ^ 2 <= 2 * r * p ^ 2 * q ^ 2 := by
    have hpSq : 1 <= p ^ 2 := by nlinarith only [hp, hp0]
    have h := mul_le_mul_of_nonneg_right hpSq
      (show 0 <= 2 * r * q ^ 2 by positivity)
    nlinarith only [h]
  refine And.intro hRef.1 (And.intro hRef.2.1 ?_)
  intro i j
  have h := hamiltonianScalingPerturbation_entry_bound P C z q qNew
    (20 * t) (a * q) (by positivity) hAq hZPoint hP hC i j
  calc
    _ <= (2 * (20 * t) + (20 * t) ^ 2) * (a * q) + abs (q - qNew) := h
    _ <= 41 * t * (p * q) + 2 * r * q ^ 2 := add_le_add hMain hRef.2.2
    _ <= 41 * t * (p * q) + 2 * r * p ^ 2 * q ^ 2 :=
      add_le_add (le_refl _) hComplement
    _ = 43 * r * p ^ 2 * q ^ 2 := by dsimp only [t]; ring
    _ <= _ := by change _ <= 44 * r * p ^ 2 * q ^ 2; nlinarith only [mul_nonneg (mul_nonneg hr (sq_nonneg p)) (sq_nonneg q)]

end PrimeFactorOscillations
