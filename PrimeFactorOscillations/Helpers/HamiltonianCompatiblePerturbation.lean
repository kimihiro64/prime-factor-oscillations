/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteRowInverse
import PrimeFactorOscillations.Helpers.HamiltonianMixingResolvent

/-! # Perturbing the full compatible inverse without losing the parity mode

The reference inverse solves J0*K=I-W. A small row perturbation E with
W*E=0 is absorbed by one full matrix inverse. The projection correction
survives exactly, and the row cost increases by at most a factor two.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianCompatibleInverse (K E : Matrix Iota Iota Real) : Matrix Iota Iota Real :=
  K * Ring.inverse ((1 : Matrix Iota Iota Real) + E * K)

theorem hamiltonian_compatible_inverse_perturbation
    (J0 K E W : Matrix Iota Iota Real) (g e : Real)
    (hg : 0 <= g) (he : 0 <= e)
    (hK : forall i, hamiltonianRowMass K i <= g)
    (hE : forall i, hamiltonianRowMass E i <= e)
    (hSmall : e * g <= 1 / 2)
    (hRight : J0 * K = 1 - W) (hCompatibility : W * E = 0) :
    (J0 + E) * hamiltonianCompatibleInverse K E = 1 - W /\
      forall i, hamiltonianRowMass (hamiltonianCompatibleInverse K E) i <= 2 * g := by
  let M : Matrix Iota Iota Real := 1 + E * K
  have hPerturb : forall i, Finset.univ.sum (fun j => abs ((M - 1) i j)) <= 1 / 2 := by
    intro i
    have hDiff : M - 1 = E * K := by dsimp only [M]; abel
    rw [hDiff]
    change hamiltonianRowMass (E * K) i <= _
    exact (hamiltonian_row_mass_mul E K g hK i).trans
      ((mul_le_mul_of_nonneg_right (hE i) hg).trans hSmall)
  have hInv := matrix_row_half_inverse M hPerturb
  have hCancel : M * Ring.inverse M = 1 := Ring.mul_inverse_cancel _ hInv.1
  have hWEK : W * (E * K) = 0 := by rw [<- mul_assoc, hCompatibility, zero_mul]
  have hWM : W * M = W := by
    dsimp only [M]
    rw [mul_add, mul_one, hWEK, add_zero]
  have hWInv : W * Ring.inverse M = W := by
    calc
      _ = (W * M) * Ring.inverse M := by rw [hWM]
      _ = W * (M * Ring.inverse M) := mul_assoc _ _ _
      _ = W := by rw [hCancel, mul_one]
  have hJK : (J0 + E) * K = M - W := by
    rw [add_mul, hRight]
    dsimp only [M]
    abel
  constructor
  . change (J0 + E) * (K * Ring.inverse M) = 1 - W
    rw [<- mul_assoc, hJK, sub_mul, hCancel, hWInv]
  . intro i
    change hamiltonianRowMass (K * Ring.inverse M) i <= _
    exact (hamiltonian_row_mass_mul K (Ring.inverse M) 2 hInv.2 i).trans
      (by nlinarith only [hK i])

end PrimeFactorOscillations
