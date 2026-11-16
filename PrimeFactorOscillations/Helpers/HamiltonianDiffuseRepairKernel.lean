/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMixingResolvent
import PrimeFactorOscillations.Helpers.HamiltonianRepairInverse

/-! # Logarithmic diffuseness bound for the actual parity repair inverse

The power prefix and first-step smoothing are discharged from the actual
stochastic rows, columns and entry cap. Both constant and parity corrections
remain in the repair kernel. The resulting inverse costs log(a), not a.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_repair_kernel_logarithmic_row (T : Matrix Iota Iota Real)
    (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (i : Sum Iota Iota) :
    (1 - rho) * hamiltonianRowMass (hamiltonianRepairKernel T q) i <=
      2 * (1 - rho) * (Real.log (2 * a) / (-Real.log rho) + 3) + 1 := by
  let B := centeredKernel T q
  let P := bipartiteLift T
  let A := bipartiteLift (averagingKernel (Iota := Iota) q)
  let Q := -P - (-A)
  let H := hamiltonianRepairProjection (Iota := Iota) q
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hCardQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hBRow (j : Iota) : Finset.univ.sum (fun k => B j k) = 0 := by
    change Finset.univ.sum (fun k => T j k - q) = 0
    rw [Finset.sum_sub_distrib, hRow j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hBCol (k : Iota) : Finset.univ.sum (fun j => B j k) = 0 := by
    change Finset.univ.sum (fun j => T j k - q) = 0
    rw [Finset.sum_sub_distrib, hCol k, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hQ : Q = -bipartiteLift B := by
    ext j k
    cases j <;> cases k <;>
      simp [Q, P, A, B, centeredKernel, averagingKernel, bipartiteLift,
        Matrix.fromBlocks, Matrix.transpose_apply] <;> ring
  have hZA : bipartiteLift B * A = 0 := by
    ext j k
    cases j <;> cases k <;>
      simp [A, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, averagingKernel, Matrix.transpose_apply,
        <- Finset.sum_mul, hBRow, hBCol]
  have hAZ : A * bipartiteLift B = 0 := by
    ext j k
    cases j <;> cases k <;>
      simp [A, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, averagingKernel, Matrix.transpose_apply,
        <- Finset.mul_sum, hBRow, hBCol]
  have hQA : Q * (-A) = 0 := by rw [hQ, neg_mul_neg, hZA]
  have hAQ : (-A) * Q = 0 := by rw [hQ, neg_mul_neg, hAZ]
  have hPN (j k : Sum Iota Iota) : 0 <= P j k := by
    cases j <;> cases k <;>
      simp [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hNonneg]
  have hPRow (j : Sum Iota Iota) : hamiltonianRowMass (-P) j <= 1 := by
    rw [hamiltonian_row_mass_neg]
    unfold hamiltonianRowMass
    simp only [abs_of_nonneg (hPN j _)]
    cases j with
    | inl j => simpa [P, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using (hRow j).le
    | inr j => simpa [P, bipartiteLift, Matrix.fromBlocks,
        Matrix.transpose_apply, Fintype.sum_sum_type] using (hCol j).le
  have hAN (j k : Sum Iota Iota) : 0 <= A j k := by
    cases j <;> cases k <;>
      simp [A, bipartiteLift, Matrix.fromBlocks, averagingKernel, hq0]
  have hARow (j : Sum Iota Iota) : hamiltonianRowMass (-A) j <= 1 := by
    rw [hamiltonian_row_mass_neg]
    unfold hamiltonianRowMass
    simp only [abs_of_nonneg (hAN j _)]
    cases j <;>
      simp [A, bipartiteLift, Matrix.fromBlocks, averagingKernel,
        Matrix.transpose_apply, Fintype.sum_sum_type, hq]
  have hPrefix (k : Nat) (j : Sum Iota Iota) : hamiltonianRowMass (Q ^ k) j <= 2 := by
    have h := hamiltonian_centered_power_row_bound (-P) (-A) 1 (by norm_num)
      hPRow hARow hQA hAQ k j
    norm_num only [one_pow] at h
    exact h
  have hQNorm : norm Q <= rho := by
    rw [hQ, norm_neg]
    exact (bipartiteLift_l2_norm_le B).trans hNorm
  have hEnergy (j : Sum Iota Iota) :
      Finset.univ.sum (fun k => Q j k ^ 2) <= (a - 1) * q := by
    rw [hQ]
    cases j with
    | inl j =>
      simpa [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
        Fintype.sum_sum_type] using stochastic_row_energy T q a hq hRow hNonneg hUpper j
    | inr j =>
      simpa [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
        Fintype.sum_sum_type] using stochastic_column_energy T q a hq hCol hNonneg hUpper j
  have hSmooth (j : Sum Iota Iota) :
      Real.sqrt (Fintype.card (Sum Iota Iota) : Real) *
        norm (WithLp.toLp 2 (fun k => Q j k) : EuclideanSpace Real (Sum Iota Iota)) <= 2 * a := by
    let v : EuclideanSpace Real (Sum Iota Iota) := WithLp.toLp 2 (fun k => Q j k)
    let m : Real := Fintype.card (Sum Iota Iota)
    have hV : norm v ^ 2 <= (a - 1) * q := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hEnergy j
    have hScaled : m * norm v ^ 2 <= 2 * (a - 1) := by
      calc
        _ <= m * ((a - 1) * q) := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
        _ = (a - 1) * (m * q) := by ring
        _ = _ := by rw [hCardQ]; ring
    have hSquare : (Real.sqrt m * norm v) ^ 2 <= 2 * (a - 1) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Sum Iota Iota)))]
      exact hScaled
    change Real.sqrt m * norm v <= 2 * a
    nlinarith only [hSquare, ha, sq_nonneg (a - 1),
      mul_nonneg (Real.sqrt_nonneg m) (norm_nonneg v)]
  have hInverse := hamiltonian_resolvent_logarithmic_row_bound Q rho 2 (2 * a)
    hQNorm hRho0 hRho1 (by norm_num) (by linarith only [ha]) hPrefix hSmooth i
  have hHRow : hamiltonianRowMass H i <= 3 / 2 := by
    calc
      _ <= Finset.univ.sum (fun _ : Sum Iota Iota => 3 * q / 4) :=
        Finset.sum_le_sum (fun j _ => hamiltonianRepairProjection_entry q hq0 i j)
      _ = (Fintype.card (Sum Iota Iota) : Real) * (3 * q / 4) := by simp
      _ = 3 / 2 := by nlinarith only [hCardQ]
  have hK : hamiltonianRepairKernel T q =
      Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Q) - H := by
    rw [hQ, sub_neg_eq_add]
    rfl
  have hMass := hamiltonian_row_mass_sub
    (Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Q)) H i
  rw [<- hK] at hMass
  have hScaled := mul_le_mul_of_nonneg_left hMass (sub_pos.mpr hRho1).le
  have hHScaled := mul_le_mul_of_nonneg_left hHRow (sub_pos.mpr hRho1).le
  nlinarith only [hScaled, hHScaled, hInverse, hRho1]

end PrimeFactorOscillations
