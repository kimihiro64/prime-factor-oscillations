/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianJointCutTail
import PrimeFactorOscillations.Helpers.HamiltonianStochasticEnergy

/-! # Joint good cuts for one actual centered stochastic kernel

The full centering subtraction is retained in every column energy.
The row event and spectral event therefore apply to the same original P
and its actual E=P-J/N, with the proved finite conditioning costs.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem hamiltonian_stochastic_symmetric_column_sum
    (P : Matrix I I Real) (hP : P.transpose = P)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1) (j : I) :
    Finset.univ.sum (fun i => P i j) = 1 := by
  have hEntry (i : I) : P i j = P j i :=
    congrArg (fun M : Matrix I I Real => M j i) hP
  simp_rw [hEntry]
  exact hRows j

theorem hamiltonian_stochastic_centered_symmetric
    (P : Matrix I I Real) (q : Real) (hP : P.transpose = P) :
    (centeredKernel P q).transpose = centeredKernel P q := by
  ext i j
  change P j i - q = P i j - q
  have hEntry : P j i = P i j := congrArg (fun M : Matrix I I Real => M i j) hP
  exact congrArg (fun x : Real => x - q) hEntry

theorem hamiltonian_stochastic_centered_hermitian
    (P : Matrix I I Real) (q : Real) (hP : P.transpose = P) :
    (centeredKernel P q).IsHermitian := by
  change (centeredKernel P q).conjTranspose = centeredKernel P q
  ext i j
  change P j i - q = P i j - q
  have hEntry : P j i = P i j := congrArg (fun M : Matrix I I Real => M i j) hP
  exact congrArg (fun x : Real => x - q) hEntry

theorem hamiltonian_stochastic_centered_column_energy
    (P : Matrix I I Real) (q alpha : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha) (j : I) :
    hamiltonianColumnEnergy (centeredKernel P q) j <= alpha - q := by
  have hCol := hamiltonian_stochastic_symmetric_column_sum P hP hRows j
  have hVariance := hamiltonian_scalar_row_variance_bound
    (fun i => P i j) alpha (fun i => hNonneg i j) (fun i => hCap i j) hCol
  change Finset.univ.sum (fun i => (P i j - q) ^ 2) <= alpha - q
  rw [centeredProbabilityEnergy_eq Finset.univ (fun i => P i j) q hCol
    (by simpa only [Finset.card_univ] using hq)]
  exact sub_le_sub_right hVariance q

theorem hamiltonian_stochastic_centered_column_cap
    (P : Matrix I I Real) (q alpha : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha) (j : I) :
    hamiltonianColumnEnergy (centeredKernel P q) j <= alpha := by
  have hn : 0 < (Fintype.card I : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hn]
  exact (hamiltonian_stochastic_centered_column_energy
    P q alpha hq hP hRows hNonneg hCap j).trans (by linarith only [hq0])

theorem hamiltonian_stochastic_joint_cut_polynomial_tail
    (P : Matrix I I Real) (q alpha A : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hNorm : norm (centeredKernel P q) <= 1) (hSize : 2 <= Fintype.card I) :
    ((hamiltonianJointCutBadSigns (centeredKernel P q) P alpha A).card : Real) /
      (Fintype.card (I -> Bool) : Real) <= (Fintype.card I : Real) ^ (-(A + 3)) := by
  exact hamiltonian_joint_cut_uniform_polynomial_tail (centeredKernel P q) P
    (hamiltonian_stochastic_centered_hermitian P q hP) alpha A hAlpha hA
    (hamiltonian_stochastic_centered_column_cap P q alpha hq hP hRows hNonneg hCap)
    hNorm hNonneg hCap hRows hSize

theorem hamiltonian_stochastic_balanced_joint_tail
    (P : Matrix I I Real) (q alpha A : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hAlpha : 0 <= alpha) (hA : 0 < A) (hNorm : norm (centeredKernel P q) <= 1)
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianJointCutBadSigns (centeredKernel P q) P alpha A)
      (hamiltonianBalancedSigns (I := I) m)).card : Real) /
        ((hamiltonianBalancedSigns (I := I) m).card : Real) <= (Fintype.card I : Real) ^ (-A) := by
  exact hamiltonian_balanced_joint_cut_polynomial_tail (centeredKernel P q) P
    (hamiltonian_stochastic_centered_hermitian P q hP) alpha A hAlpha hA
    (hamiltonian_stochastic_centered_column_cap P q alpha hq hP hRows hNonneg hCap)
    hNorm hNonneg hCap hRows m hm hSize

theorem hamiltonian_stochastic_prescribed_joint_tail
    (P : Matrix I I Real) (q alpha A : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hAlpha : 0 <= alpha) (hA : 0 < A) (hNorm : norm (centeredKernel P q) <= 1)
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianJointCutBadSigns (centeredKernel P q) P alpha A)
      (hamiltonianPrescribedBalancedSigns m a b)).card : Real) /
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  exact hamiltonian_prescribed_joint_cut_polynomial_tail (centeredKernel P q) P
    (hamiltonian_stochastic_centered_hermitian P q hP) alpha A hAlpha hA
    (hamiltonian_stochastic_centered_column_cap P q alpha hq hP hRows hNonneg hCap)
    hNorm hNonneg hCap hRows a b hab m hm hSize

end PrimeFactorOscillations
