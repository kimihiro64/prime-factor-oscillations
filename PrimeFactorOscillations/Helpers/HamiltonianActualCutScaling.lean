/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedCutCoordinates
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseSpectralScaling
import PrimeFactorOscillations.Helpers.HamiltonianInverseDegreeNormalization
import PrimeFactorOscillations.Helpers.HamiltonianStochasticCutTail

/-! # Positive scaling of the same actual good complementary cut

The joint finite event supplies the actual centered cross gap and all degrees.
The maintained nonlinear scaling theorem repairs precisely that cross block,
with its support, entry cap, operator gap and common multiplier witness.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype J] [DecidableEq J] [Nonempty J]

theorem hamiltonian_stochastic_cap_mass
    (P : Matrix I I Real) (alpha : Real)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCap : forall i j, P i j <= alpha) :
    1 <= (Fintype.card I : Real) * alpha := by
  let i : I := Classical.choice inferInstance
  have h := Finset.sum_le_sum (fun j (_ : Membership.mem Finset.univ j) => hCap i j)
  rw [hRows, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h

theorem hamiltonian_actual_good_cross_bounds
    (P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hSize : Fintype.card I = 2 * Fintype.card J)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel P (1 / (Fintype.card I : Real))) <= 1 - delta)
    (hThreshold : Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <=
      delta / 128)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A) e)) :
    let T := hamiltonianBalancedCrossBlock P e l r
    let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))
    norm (centeredKernel T (1 / (Fintype.card J : Real))) <= 1 - 3 * delta / 4 /\
      (forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps) /\
      (forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps) := by
  have h := hamiltonian_good_joint_cut_gap_and_rows
    (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A delta e
    (hamiltonian_stochastic_centered_symmetric P _ hP) hDelta hDelta1 hNorm
    hRows hThreshold hGood
  have hRef := hamiltonian_balanced_reference_factor (I := I) (J := J) hSize
  have hCross := hamiltonian_balanced_cross_centered_norm P e l r
    (1 / (Fintype.card I : Real))
  rw [hRef] at hCross
  have hDegrees := hamiltonian_balanced_cross_degree_defects P e l r hP
    (Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))) h.2
  exact And.intro (hCross.trans h.1) hDegrees

theorem hamiltonian_actual_good_cross_normalized_gap
    (P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hSize : Fintype.card I = 2 * Fintype.card J)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel P (1 / (Fintype.card I : Real))) <= 1 - delta)
    (hThreshold : Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <=
      delta / 128)
    (hEpsMargin : 64 * Real.sqrt
      (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <= delta)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A) e)) :
    let T := hamiltonianBalancedCrossBlock P e l r
    norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T (1 / (Fintype.card J : Real))) <=
        1 - delta / 2 := by
  let T := hamiltonianBalancedCrossBlock P e l r
  let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))
  have he : 0 <= eps := Real.sqrt_nonneg _
  have he1 : eps <= 1 / 2 := by
    change 64 * eps <= delta at hEpsMargin
    linarith only [hEpsMargin, hDelta1]
  have hn : 0 < (Fintype.card J : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq : (Fintype.card J : Real) * (1 / (Fintype.card J : Real)) = 1 := by
    field_simp [ne_of_gt hn]
  have h := hamiltonian_actual_good_cross_bounds P alpha A delta e l r
    hP hRows hSize hDelta hDelta1 hNorm hThreshold hGood
  have hNormalized := hamiltonian_actual_raw_to_normalized_degree_gap
    T (1 / (Fintype.card J : Real)) eps (1 - 3 * delta / 4) hq he he1
    (by linarith only [hDelta1]) (by linarith only [hDelta]) h.2.1 h.2.2 h.1
  change 64 * eps <= delta at hEpsMargin
  change norm (hamiltonianActualDegreeNormalizedCross T -
    hamiltonianActualDegreeNormalizedMode T (1 / (Fintype.card J : Real))) <= _
  linarith only [hNormalized, hEpsMargin]

theorem hamiltonian_actual_good_cut_positive_scaling
    (P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hSize : Fintype.card I = 2 * Fintype.card J)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel P (1 / (Fintype.card I : Real))) <= 1 - delta)
    (hThreshold : Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <=
      delta / 128)
    (hEps : Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <= 1 / 2)
    (hSmall : Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) *
      Real.log (4 * ((Fintype.card I : Real) * alpha)) ^ 2 <=
        hamiltonianNormalizedScalingSmall (delta / 2))
    (hCost : hamiltonianNormalizedScalingCost (delta / 2) *
      Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) *
        Real.log (4 * ((Fintype.card I : Real) * alpha)) <= delta / 4)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A) e)) :
    let T := hamiltonianBalancedCrossBlock P e l r
    let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))
    let K := hamiltonianNormalizedScalingCost (delta / 2) *
      eps * Real.log (4 * ((Fintype.card I : Real) * alpha))
    exists z : Sum J J -> Real,
      norm z <= K /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 4 * alpha) /\
      norm (hamiltonianScaledCross T z - T) <= K /\
      norm (centeredKernel (hamiltonianScaledCross T z)
        (1 / (Fintype.card J : Real))) <= 1 - delta / 2 := by
  let T := hamiltonianBalancedCrossBlock P e l r
  let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))
  let a := (Fintype.card I : Real) * alpha
  have he : 0 <= eps := Real.sqrt_nonneg _
  have ha : 1 <= a := hamiltonian_stochastic_cap_mass P alpha hRows hCap
  have hControl := hamiltonian_actual_good_cross_bounds P alpha A delta e l r
    hP hRows hSize hDelta hDelta1 hNorm hThreshold hGood
  have hEntry (i j : J) := hamiltonian_balanced_cross_entry_bounds P e l r alpha hNonneg hCap i j
  have hn : Not ((Fintype.card J : Real) = 0) :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hSizeReal : (Fintype.card I : Real) = 2 * (Fintype.card J : Real) := by
    exact_mod_cast hSize
  have hCapId : a * (1 / (Fintype.card J : Real)) = 2 * alpha := by
    dsimp only [a]
    rw [hSizeReal]
    field_simp [hn]
    <;> ring
  have hUpper (i j : J) : T i j <= a * (1 / (Fintype.card J : Real)) := by
    rw [hCapId]
    exact (hEntry i j).2
  have hRaw : norm (centeredKernel T (1 / (Fintype.card J : Real))) <=
      1 - delta / 2 + 8 * eps := by
    have h := hControl.1
    change norm (centeredKernel T (1 / (Fintype.card J : Real))) <= 1 - 3 * delta / 4 at h
    linarith only [h, hDelta, he]
  choose z hz hPos hNonnegScaled hRow hCol hSupport hScaledCap hError using
    hamiltonian_centered_gap_diffuse_scaling T a (delta / 2) eps ha
      (by linarith only [hDelta]) (by linarith only [hDelta1]) he hEps
      (fun i j => (hEntry i j).1) hUpper hControl.2.1 hControl.2.2 hRaw hSmall
  refine Exists.intro z (And.intro hz (And.intro hPos (And.intro hNonnegScaled
    (And.intro hRow (And.intro hCol (And.intro hSupport (And.intro ?_
      (And.intro hError ?_))))))))
  . intro i j
    exact (hScaledCap i j).trans (by
      have h := (hEntry i j).2
      change 2 * T i j <= 4 * alpha
      linarith only [h])
  . have hTriangle := norm_sub_le_norm_sub_add_norm_sub
      (hamiltonianScaledCross T z) T
      (averagingKernel (1 / (Fintype.card J : Real)) : Matrix J J Real)
    change norm (centeredKernel (hamiltonianScaledCross T z)
      (1 / (Fintype.card J : Real))) <= _
    have hRawGap := hControl.1
    change norm (centeredKernel T (1 / (Fintype.card J : Real))) <=
      1 - 3 * delta / 4 at hRawGap
    change norm (hamiltonianScaledCross T z - T) <=
      hamiltonianNormalizedScalingCost (delta / 2) * eps * Real.log (4 * a) at hError
    change hamiltonianNormalizedScalingCost (delta / 2) * eps * Real.log (4 * a) <=
      delta / 4 at hCost
    change norm (centeredKernel (hamiltonianScaledCross T z)
      (1 / (Fintype.card J : Real))) <= norm (hamiltonianScaledCross T z - T) +
        norm (centeredKernel T (1 / (Fintype.card J : Real))) at hTriangle
    linarith only [hTriangle, hError, hCost, hRawGap]

end PrimeFactorOscillations
