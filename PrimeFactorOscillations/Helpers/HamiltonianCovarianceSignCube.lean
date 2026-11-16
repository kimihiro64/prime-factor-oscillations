/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianComplementaryCut
import PrimeFactorOscillations.Helpers.HamiltonianSignCubeTail

/-! # Actual complementary covariance on every sign cut

The sign cube is in bijection with all coordinate cuts. Its
random column sum is exactly the original covariance operator,
so the full moment tail transfers with no model approximation.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianSignCut (e : I -> Bool) : Finset I :=
  Finset.univ.filter (fun i => e i = true)

theorem hamiltonian_mem_sign_cut (e : I -> Bool) (i : I) :
    Membership.mem (hamiltonianSignCut e) i <-> e i = true := by
  simp [hamiltonianSignCut]

def hamiltonianSignCutEquiv : Equiv (I -> Bool) (Finset I) where
  toFun := hamiltonianSignCut
  invFun := fun D i => decide (Membership.mem D i)
  left_inv := by
    intro e
    funext i
    cases h : e i <;> simp [hamiltonian_mem_sign_cut, h]
  right_inv := by
    intro D
    ext i
    simp [hamiltonian_mem_sign_cut]

theorem hamiltonian_sign_cut_injective :
    Function.Injective (hamiltonianSignCut : (I -> Bool) -> Finset I) :=
  hamiltonianSignCutEquiv.injective

theorem hamiltonian_sign_cut_surjective :
    Function.Surjective (hamiltonianSignCut : (I -> Bool) -> Finset I) :=
  hamiltonianSignCutEquiv.surjective

theorem hamiltonian_sign_column_sum_eq_covariance
    (E : Matrix I I Real) (hE : E.transpose = E) (e : I -> Bool) :
    hamiltonianSignMatrix (hamiltonianColumnSummand E) e =
      hamiltonianComplementaryCovariance E (hamiltonianCutProjection (hamiltonianSignCut e)) := by
  ext i j
  rw [hamiltonian_cut_covariance_entry]
  simp only [hamiltonianSignMatrix, Matrix.sum_apply, hamiltonian_sign_smul_entry,
    hamiltonianColumnSummand]
  apply Finset.sum_congr rfl
  intro k hk
  have hSym : E j k = E k j := congrArg (fun M : Matrix I I Real => M k j) hE
  rw [hSym]
  have hCoeff : hamiltonianSignValue (e k) / 2 =
      (if Membership.mem (hamiltonianSignCut e) k then (1 : Real) else 0) - 1 / 2 := by
    cases h : e k <;> norm_num [hamiltonian_mem_sign_cut, hamiltonianSignValue, h]
  calc
    _ = (hamiltonianSignValue (e k) / 2) * E i k * E k j := by ring
    _ = _ := by rw [hCoeff]

theorem hamiltonian_actual_covariance_sign_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) (hk : 1 <= k)
    (t : Real) (ht : 0 < t) :
    ((Finset.univ.filter (fun e : I -> Bool =>
      t < norm (hamiltonianComplementaryCovariance E
        (hamiltonianCutProjection (hamiltonianSignCut e))))).card : Real) /
        (Fintype.card (I -> Bool) : Real) <=
      ((Fintype.card I : Real) * (alpha * (k : Real) / 2) ^ k) / t ^ (2 * k) := by
  classical
  have hET : E.transpose = E := by
    ext i j
    have h : E.conjTranspose = E := hE
    simpa using congrArg (fun M : Matrix I I Real => M i j) h
  have hSets : Finset.univ.filter (fun e : I -> Bool =>
      t < norm (hamiltonianComplementaryCovariance E
        (hamiltonianCutProjection (hamiltonianSignCut e)))) =
        hamiltonianColumnBadSigns E t := by
    ext e
    rw [hamiltonian_mem_column_bad_signs]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hamiltonian_sign_column_sum_eq_covariance E hET e]
  rw [hSets]
  exact hamiltonian_column_bad_sign_proportion_bound E hE alpha hAlpha hColumn hNorm k hk t ht

end PrimeFactorOscillations
