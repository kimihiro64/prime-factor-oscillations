/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnMoments
import PrimeFactorOscillations.Helpers.HamiltonianTraceNormReadout

/-! # A full finite covariance tail from signed column moments

The exceptional sign vectors are counted on the whole finite cube.
The operator-norm readout and nonnegative even traces are reused
from their maintained providers. No sampled finite diagnostic
is substituted for this uniform all-order bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_hermitian_norm_even_power_le_trace
    (M : Matrix I I Real) (hM : M.IsHermitian) (k : Nat) (hk : 1 <= k) :
    norm M ^ (2 * k) <= Matrix.trace (M ^ (2 * k)) := by
  let p := 2 * k
  have hp : 2 <= p := by dsimp only [p]; omega
  have hEven : Even p := Exists.intro k (by dsimp only [p]; omega)
  have hRoot := hamiltonian_hermitian_norm_le_even_trace_root M hM p hp hEven
  have hTrace := hamiltonian_even_trace_power_nonnegative M hM p hEven
  have hpPos : (0 : Real) < p := Nat.cast_pos.mpr (by omega)
  have hpNe : Not ((p : Real) = 0) := ne_of_gt hpPos
  have hExp : (1 / (p : Real)) * (p : Real) = 1 := by field_simp
  have hId : ((Matrix.trace (M ^ p)) ^ (1 / (p : Real))) ^ p =
      Matrix.trace (M ^ p) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hTrace, hExp, Real.rpow_one]
  have hPow : norm M ^ p <= ((Matrix.trace (M ^ p)) ^ (1 / (p : Real))) ^ p := by
    gcongr
  rw [hId] at hPow
  exact hPow

def hamiltonianColumnBadSigns (E : Matrix I I Real) (t : Real) : Finset (I -> Bool) := by
  classical
  exact Finset.univ.filter (fun e =>
    t < norm (hamiltonianSignMatrix (hamiltonianColumnSummand E) e))

theorem hamiltonian_mem_column_bad_signs
    (E : Matrix I I Real) (t : Real) (e : I -> Bool) :
    Membership.mem (hamiltonianColumnBadSigns E t) e <->
      t < norm (hamiltonianSignMatrix (hamiltonianColumnSummand E) e) := by
  classical
  simp [hamiltonianColumnBadSigns]

theorem hamiltonian_column_bad_sign_count_bound
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) (hk : 1 <= k)
    (t : Real) (ht : 0 < t) :
    ((hamiltonianColumnBadSigns E t).card : Real) * t ^ (2 * k) <=
      (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) *
        (alpha * (k : Real) / 2) ^ k := by
  classical
  let A := hamiltonianColumnSummand E
  let F := hamiltonianSignMatrix A
  let B := hamiltonianColumnBadSigns E t
  have hA : forall j, (A j).IsHermitian := hamiltonian_column_summand_hermitian E
  have hEven : Even (2 * k) := Exists.intro k (by omega)
  have hTrace (e : I -> Bool) : 0 <= Matrix.trace (F e ^ (2 * k)) :=
    hamiltonian_even_trace_power_nonnegative (F e)
      (hamiltonian_sign_matrix_hermitian A hA e) (2 * k) hEven
  have hSingle (e : I -> Bool) (he : Membership.mem B e) :
      t ^ (2 * k) <= Matrix.trace (F e ^ (2 * k)) := by
    have hBad := (hamiltonian_mem_column_bad_signs E t e).mp he
    have hPow : t ^ (2 * k) <= norm (F e) ^ (2 * k) := by
      gcongr <;> exact hBad.le
    exact hPow.trans (hamiltonian_hermitian_norm_even_power_le_trace (F e)
      (hamiltonian_sign_matrix_hermitian A hA e) k hk)
  calc
    _ = B.sum (fun _ => t ^ (2 * k)) := by
      change (B.card : Real) * t ^ (2 * k) = _
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= B.sum (fun e => Matrix.trace (F e ^ (2 * k))) := Finset.sum_le_sum hSingle
    _ <= Finset.univ.sum (fun e => Matrix.trace (F e ^ (2 * k))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun e he hne => hTrace e)
    _ = hamiltonianColumnMoment E k := rfl
    _ <= _ := hamiltonian_column_moment_power_bound E hE alpha hAlpha hColumn hNorm k

theorem hamiltonian_column_bad_sign_proportion_bound
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) (hk : 1 <= k)
    (t : Real) (ht : 0 < t) :
    ((hamiltonianColumnBadSigns E t).card : Real) / (Fintype.card (I -> Bool) : Real) <=
      ((Fintype.card I : Real) * (alpha * (k : Real) / 2) ^ k) / t ^ (2 * k) := by
  have hMain := hamiltonian_column_bad_sign_count_bound E hE alpha hAlpha hColumn hNorm k hk t ht
  have hCube : (0 : Real) < Fintype.card (I -> Bool) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hPower : 0 < t ^ (2 * k) := pow_pos ht _
  have h := div_le_div_of_nonneg_right hMain (mul_nonneg hCube.le hPower.le)
  convert h using 1 <;> field_simp [ne_of_gt hCube, ne_of_gt hPower]

theorem hamiltonian_zero_column_energy_matrix
    (E : Matrix I I Real) (hColumn : forall j, hamiltonianColumnEnergy E j <= 0) :
    E = 0 := by
  ext i j
  have hSingle : E i j ^ 2 <= hamiltonianColumnEnergy E j :=
    Finset.single_le_sum (f := fun r => E r j ^ 2)
      (fun r hr => sq_nonneg _) (Finset.mem_univ i)
  have hZero := hColumn j
  change E i j = 0
  nlinarith only [hSingle, hZero, sq_nonneg (E i j)]

end PrimeFactorOscillations
