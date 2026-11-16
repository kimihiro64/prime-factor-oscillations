/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeEvenGap
import PrimeFactorOscillations.Helpers.HamiltonianCycleTransport
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossBlock

/-! # The actual even coprime cross block

Parity coordinates preserve the full native kernel, its constant/parity
compensation, stochasticity and single-cycle sum. The physical half-gap
therefore applies to the actual centered cross block without dimension loss.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_fin_zmod_value {n : Nat} [NeZero n] (i : Fin n) :
    ((ZMod.finEquiv n) i).val = i.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

theorem hamiltonian_even_difference_parity {n : Nat} [NeZero n]
    (hEven : Dvd.dvd 2 n) (x y : ZMod n) :
    (x - y).val % 2 = (x.val + y.val) % 2 := by
  have hSum : ((x - y).val + y.val) % 2 = x.val % 2 := by
    rw [<- Nat.mod_mod_of_dvd ((x - y).val + y.val) hEven,
      <- ZMod.val_add (x - y) y, sub_add_cancel]
  rw [Nat.add_mod] at hSum
  rw [Nat.add_mod]
  omega

theorem hamiltonian_neg_one_power_mod_two (a : Nat) :
    (-1 : Real) ^ a = (-1 : Real) ^ (a % 2) := by
  calc
    _ = ((-1 : Real) ^ 2) ^ (a / 2) * (-1 : Real) ^ (a % 2) := by
      rw [<- pow_mul, <- pow_add]
      congr 1
      omega
    _ = _ := by norm_num

theorem hamiltonian_even_difference_neg_one_power {n : Nat} [NeZero n]
    (hEven : Dvd.dvd 2 n) (x y : ZMod n) :
    (-1 : Real) ^ (x - y).val = (-1 : Real) ^ (x.val + y.val) := by
  rw [hamiltonian_neg_one_power_mod_two (x - y).val,
    hamiltonian_neg_one_power_mod_two (x.val + y.val),
    hamiltonian_even_difference_parity hEven]

theorem hamiltonian_coprime_same_parity_zero {n : Nat} [NeZero n]
    (hEven : Dvd.dvd 2 n) (x y : ZMod n) (hParity : x.val % 2 = y.val % 2) :
    hamiltonianCoprimeKernel x y = 0 := by
  have hDiff : (x - y).val % 2 = 0 := by
    rw [hamiltonian_even_difference_parity hEven, Nat.add_mod]
    omega
  have hNotUnit : Not (IsUnit (x - y)) := by
    intro hUnit
    have hCoprime : Nat.Coprime (x - y).val n :=
      (ZMod.isUnit_iff_coprime (x - y).val n).mp
        (by simpa only [ZMod.natCast_zmod_val] using hUnit)
    have hDiv : Dvd.dvd 2 (Nat.gcd (x - y).val n) :=
      Nat.dvd_gcd (Nat.dvd_iff_mod_eq_zero.mpr hDiff) hEven
    rw [hCoprime.gcd_eq_one] at hDiv
    norm_num at hDiv
  simp only [hamiltonianCoprimeKernel, hamiltonianCoprimeAdjacency,
    hNotUnit, ite_false, zero_div]

variable (m : Nat) [NeZero m]

def hamiltonianCoprimeParityEquiv :
    Equiv (Sum (Fin m) (Fin m)) (ZMod (2 * m)) :=
  (LPF.hamiltonianParityEquiv m).trans (ZMod.finEquiv (2 * m)).toEquiv

def hamiltonianCoprimeCrossBlock : Matrix (Fin m) (Fin m) Real :=
  fun i j => hamiltonianCoprimeKernel
    (hamiltonianCoprimeParityEquiv m (Sum.inl i))
    (hamiltonianCoprimeParityEquiv m (Sum.inr j))

theorem hamiltonian_coprime_parity_equiv_value (s : Sum (Fin m) (Fin m)) :
    (hamiltonianCoprimeParityEquiv m s).val = (LPF.hamiltonianParityIndex m s).val := by
  exact hamiltonian_fin_zmod_value (LPF.hamiltonianParityIndex m s)

theorem hamiltonian_coprime_cross_reindex :
    (hamiltonianCoprimeKernel (n := 2 * m)).submatrix
      (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) =
      bipartiteLift (hamiltonianCoprimeCrossBlock m) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change hamiltonianCoprimeKernel
            (hamiltonianCoprimeParityEquiv m (Sum.inl i))
            (hamiltonianCoprimeParityEquiv m (Sum.inl j)) = 0
          apply hamiltonian_coprime_same_parity_zero (dvd_mul_right 2 m)
          rw [hamiltonian_coprime_parity_equiv_value, hamiltonian_coprime_parity_equiv_value]
          simp [LPF.hamiltonianParityIndex]
      | inr j => rfl
  | inr i =>
      cases j with
      | inl j =>
          change hamiltonianCoprimeKernel
            (hamiltonianCoprimeParityEquiv m (Sum.inr i))
            (hamiltonianCoprimeParityEquiv m (Sum.inl j)) =
              hamiltonianCoprimeKernel
                (hamiltonianCoprimeParityEquiv m (Sum.inl j))
                (hamiltonianCoprimeParityEquiv m (Sum.inr i))
          exact (congrArg (fun M : Matrix (ZMod (2 * m)) (ZMod (2 * m)) Real =>
            M (hamiltonianCoprimeParityEquiv m (Sum.inr i))
              (hamiltonianCoprimeParityEquiv m (Sum.inl j)))
            hamiltonian_coprime_kernel_symmetric).symm
      | inr j =>
          change hamiltonianCoprimeKernel
            (hamiltonianCoprimeParityEquiv m (Sum.inr i))
            (hamiltonianCoprimeParityEquiv m (Sum.inr j)) = 0
          apply hamiltonian_coprime_same_parity_zero (dvd_mul_right 2 m)
          rw [hamiltonian_coprime_parity_equiv_value, hamiltonian_coprime_parity_equiv_value]
          simp [LPF.hamiltonianParityIndex]

theorem hamiltonian_coprime_constant_parity_reindex :
    (hamiltonianCoprimeConstantParityKernel (n := 2 * m)).submatrix
      (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) =
      bipartiteLift (fun _ _ : Fin m => (1 : Real) / (m : Real)) := by
  have hEntries :
      (hamiltonianCoprimeConstantParityKernel (n := 2 * m)).submatrix
        (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) =
      (LPF.hamiltonianRealConstantParityMatrix (2 * m)).submatrix
        (LPF.hamiltonianParityEquiv m) (LPF.hamiltonianParityEquiv m) := by
    ext i j
    simp only [Matrix.submatrix_apply, hamiltonianCoprimeConstantParityKernel,
      hamiltonian_even_difference_neg_one_power (dvd_mul_right 2 m),
      hamiltonian_coprime_parity_equiv_value, LPF.hamiltonianRealConstantParityMatrix]
    change (1 - (-1 : Real) ^ ((LPF.hamiltonianParityIndex m i).val +
      (LPF.hamiltonianParityIndex m j).val)) / (2 * m : Nat) =
        (1 - (-1 : Real) ^ (((LPF.hamiltonianParityIndex m i).val + 1) +
          ((LPF.hamiltonianParityIndex m j).val + 1))) / (2 * m : Nat)
    simp only [pow_add, pow_one]
    ring
  rw [hEntries]
  exact LPF.hamiltonian_constant_parity_reindex m (by have hPos := NeZero.pos m; omega)

theorem hamiltonian_coprime_cross_row_sum (i : Fin m) :
    Finset.univ.sum (fun j => hamiltonianCoprimeCrossBlock m i j) = 1 := by
  have h := hamiltonian_sum_reindex (hamiltonianCoprimeParityEquiv m)
    (fun k => hamiltonianCoprimeKernel (hamiltonianCoprimeParityEquiv m (Sum.inl i)) k)
  have hs : Finset.univ.sum (fun s =>
      hamiltonianCoprimeKernel (hamiltonianCoprimeParityEquiv m (Sum.inl i))
        (hamiltonianCoprimeParityEquiv m s)) =
      Finset.univ.sum (fun j => hamiltonianCoprimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s => ((hamiltonianCoprimeKernel (n := 2 * m)).submatrix
      (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m)) (Sum.inl i) s) = _
    rw [hamiltonian_coprime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type]
  exact hs.symm.trans (h.trans (hamiltonian_coprime_kernel_row_sum _))

theorem hamiltonian_coprime_cross_col_sum (j : Fin m) :
    Finset.univ.sum (fun i => hamiltonianCoprimeCrossBlock m i j) = 1 := by
  have h := hamiltonian_sum_reindex (hamiltonianCoprimeParityEquiv m)
    (fun k => hamiltonianCoprimeKernel k (hamiltonianCoprimeParityEquiv m (Sum.inr j)))
  have hs : Finset.univ.sum (fun s =>
      hamiltonianCoprimeKernel (hamiltonianCoprimeParityEquiv m s)
        (hamiltonianCoprimeParityEquiv m (Sum.inr j))) =
      Finset.univ.sum (fun i => hamiltonianCoprimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s => ((hamiltonianCoprimeKernel (n := 2 * m)).submatrix
      (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m)) s (Sum.inr j)) = _
    rw [hamiltonian_coprime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type]
  exact hs.symm.trans (h.trans (hamiltonian_coprime_kernel_col_sum _))

theorem hamiltonian_coprime_cross_nonnegative (i j : Fin m) :
    0 <= hamiltonianCoprimeCrossBlock m i j :=
  hamiltonian_coprime_kernel_nonnegative _ _

theorem hamiltonian_coprime_cross_entry_cap (i j : Fin m) :
    hamiltonianCoprimeCrossBlock m i j <= 1 / ((2 * m).totient : Real) :=
  hamiltonian_coprime_kernel_entry_cap _ _

theorem hamiltonian_coprime_cross_physical_gap :
    norm (centeredKernel (hamiltonianCoprimeCrossBlock m) (1 / (m : Real))) <=
      (1 / 2 : Real) := by
  have hEq :
      (hamiltonianCoprimeKernel (n := 2 * m) - hamiltonianCoprimeConstantParityKernel).submatrix
        (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) =
      bipartiteLift (centeredKernel (hamiltonianCoprimeCrossBlock m) (1 / (m : Real))) := by
    change (hamiltonianCoprimeKernel (n := 2 * m)).submatrix
      (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) -
      (hamiltonianCoprimeConstantParityKernel (n := 2 * m)).submatrix
        (hamiltonianCoprimeParityEquiv m) (hamiltonianCoprimeParityEquiv m) = _
    rw [hamiltonian_coprime_cross_reindex, hamiltonian_coprime_constant_parity_reindex]
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, centeredKernel, averagingKernel,
        Matrix.sub_apply, Matrix.transpose]
  have hNorm := @hamiltonian_reindex_matrix_norm
    (ZMod (2 * m)) (Sum (Fin m) (Fin m))
    (inferInstance : Fintype (ZMod (2 * m))) (inferInstance : Fintype (Sum (Fin m) (Fin m)))
    (inferInstance : DecidableEq (ZMod (2 * m))) (inferInstance : DecidableEq (Sum (Fin m) (Fin m)))
    (hamiltonianCoprimeParityEquiv m)
    (hamiltonianCoprimeKernel (n := 2 * m) - hamiltonianCoprimeConstantParityKernel)
  rw [hEq, hamiltonian_bipartite_lift_norm] at hNorm
  exact hNorm.le.trans (hamiltonian_coprime_even_physical_gap (dvd_mul_right 2 m))

theorem hamiltonian_coprime_cross_cycle_sum :
    hamiltonianCycleSum (hamiltonianCoprimeKernel (n := 2 * m)) =
      hamiltonianCycleSum (bipartiteLift (hamiltonianCoprimeCrossBlock m)) := by
  have h := hamiltonian_cycle_sum_reindex (hamiltonianCoprimeParityEquiv m)
    (hamiltonianCoprimeKernel (n := 2 * m))
  rw [hamiltonian_coprime_cross_reindex] at h
  exact h.symm

end PrimeFactorOscillations
