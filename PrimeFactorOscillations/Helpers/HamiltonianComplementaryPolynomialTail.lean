/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnPolynomialTail
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceSignCube

/-! # The actual complementary-cut polynomial covariance estimate

The uniform full-cube tail is transported by the exact operator
identity. The deterministic quarter and fixed-gap consumers use
the same covariance, with every coordinate and cross term retained.
Balanced conditioning is a separate counting obligation.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_covariance_bad_signs_eq
    (E : Matrix I I Real) (hE : E.IsHermitian) (t : Real) :
    Finset.univ.filter (fun e : I -> Bool =>
      t < norm (hamiltonianComplementaryCovariance E
        (hamiltonianCutProjection (hamiltonianSignCut e)))) =
      hamiltonianColumnBadSigns E t := by
  classical
  have hET : E.transpose = E := by
    ext i j
    have h : E.conjTranspose = E := hE
    simpa using congrArg (fun M : Matrix I I Real => M i j) h
  ext e
  rw [hamiltonian_mem_column_bad_signs]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hamiltonian_sign_column_sum_eq_covariance E hET e]

theorem hamiltonian_actual_covariance_uniform_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (hSize : 2 <= Fintype.card I) :
    ((Finset.univ.filter (fun e : I -> Bool =>
      Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))) <
        norm (hamiltonianComplementaryCovariance E
          (hamiltonianCutProjection (hamiltonianSignCut e))))).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) ^ (-(A + 3)) := by
  rw [hamiltonian_covariance_bad_signs_eq E hE]
  exact hamiltonian_column_uniform_polynomial_tail E hE alpha A hAlpha hA hColumn hNorm hSize

theorem hamiltonian_complementary_quarter_failure_inclusion
    (E : Matrix I I Real) (hE : E.transpose = E) (t : Real) :
    Finset.univ.filter (fun e : I -> Bool =>
      norm E ^ 2 / 4 + (3 / 2 : Real) * t <
        norm (E.submatrix (fun i : hamiltonianSignCut e => i.val)
          (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) ^ 2) <=
      Finset.univ.filter (fun e : I -> Bool =>
        t < norm (hamiltonianComplementaryCovariance E
          (hamiltonianCutProjection (hamiltonianSignCut e)))) := by
  classical
  intro e he
  have hBad := (Finset.mem_filter.mp he).2
  apply Finset.mem_filter.mpr
  apply And.intro (Finset.mem_univ _)
  have hBound := hamiltonian_actual_complementary_restriction_quarter E (hamiltonianSignCut e) hE
  by_contra hNot
  have hCov := le_of_not_gt hNot
  nlinarith only [hBad, hBound, hCov]

theorem hamiltonian_actual_complementary_quarter_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (hSize : 2 <= Fintype.card I) :
    ((Finset.univ.filter (fun e : I -> Bool =>
      norm E ^ 2 / 4 + (3 / 2 : Real) *
          Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))) <
        norm (E.submatrix (fun i : hamiltonianSignCut e => i.val)
          (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) ^ 2)).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) ^ (-(A + 3)) := by
  have hET : E.transpose = E := by
    ext i j
    have h : E.conjTranspose = E := hE
    simpa using congrArg (fun M : Matrix I I Real => M i j) h
  have hSubset := hamiltonian_complementary_quarter_failure_inclusion E hET
    (Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))))
  have hCast (B C : Finset (I -> Bool)) (hBC : B <= C) :
      (B.card : Real) <= (C.card : Real) := Nat.cast_le.mpr (Finset.card_le_card hBC)
  have hCard := hCast _ _ hSubset
  exact (div_le_div_of_nonneg_right hCard (Nat.cast_nonneg _)).trans
    (hamiltonian_actual_covariance_uniform_polynomial_tail
      E hE alpha A hAlpha hA hColumn hNorm hSize)

theorem hamiltonian_complementary_gap_failure_inclusion
    (E : Matrix I I Real) (hE : E.transpose = E) (delta t : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hNorm : norm E <= 1 - delta)
    (hThreshold : t <= delta / 128) :
    Finset.univ.filter (fun e : I -> Bool =>
      1 - 3 * delta / 4 <
        2 * norm (E.submatrix (fun i : hamiltonianSignCut e => i.val)
          (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val))) <=
      Finset.univ.filter (fun e : I -> Bool =>
        t < norm (hamiltonianComplementaryCovariance E
          (hamiltonianCutProjection (hamiltonianSignCut e)))) := by
  classical
  intro e he
  have hBad := (Finset.mem_filter.mp he).2
  apply Finset.mem_filter.mpr
  apply And.intro (Finset.mem_univ _)
  by_contra hNot
  have hCov := (le_of_not_gt hNot).trans hThreshold
  have hBound := hamiltonian_actual_complementary_cut_gap E (hamiltonianSignCut e)
    delta hE hDelta hDelta1 hNorm hCov
  exact (not_lt_of_ge hBound) hBad

end PrimeFactorOscillations
