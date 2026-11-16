/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalModelBlocks

/-! # The complete nonexceptional rational-model norm

Geometric separation bounds the actual sampling Gram error. Both signed
character frames and the full nonexceptional Mobius diagonal are kept.
Only the denominator-one and denominator-two blocks are excluded, and
the remaining physical operator is bounded by 1/2 + 2 Q^4/n.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_rational_center_kernel {R : Nat} [NeZero R]
    (n Q : Nat) (hQ : 0 < Q) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R)
    (u v : lpfRationalCenters Q) (huv : Not (u = v)) :
    norm (lpfIntervalFrequencyKernel R 0 n
      (hamiltonianRationalCenter R Q v - hamiltonianRationalCenter R Q u)) <=
        4 * (Q : Real) ^ 2 := by
  let D := R / (4 * Q ^ 2)
  have hRadius := hamiltonian_reference_physical_radius R Q 1
    (Nat.pos_of_ne_zero (NeZero.ne R)) hQ (by decide) (dvd_refl R) (by simpa using hRange)
  have hW : (R / R) * 1 = 1 := by
    simp only [Nat.div_self (NeZero.pos R), mul_one]
  rw [hW] at hRadius
  have hD : 1 <= D := hRadius.2.1
  have hFar : Not (Membership.mem (lpfIntervalOffsetGrid R D)
      (hamiltonianRationalCenter R Q v - hamiltonianRationalCenter R Q u)) := by
    have h := hamiltonian_rational_other_center_far Q 0 D (Nat.zero_le D)
      hDiv hRadius.2.2.1 v u (fun hEq => huv hEq.symm) 0 (by simp)
    simpa only [hamiltonian_packet_point_eq, Int.cast_zero, add_zero] using h
  exact (hamiltonian_interval_kernel_outside 0 n D hD _ hFar).trans hRadius.2.2.2

theorem hamiltonian_rational_frame_norms {R : Nat} [NeZero R]
    (n Q : Nat) (hQ : 0 < Q) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R) :
    And
      (norm (hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R Q)) *
          norm (hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R Q)) <=
        (n : Real) + 4 * (Q : Real) ^ 4)
      (norm (hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R Q u)) *
          norm (hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R Q u)) <=
        (n : Real) + 4 * (Q : Real) ^ 4) := by
  have hCard : (Fintype.card (lpfRationalCenters Q) : Real) <= (Q : Real) ^ 2 := by
    exact_mod_cast lpfRationalCenters_card_le Q
  have hScale : (n : Real) + (Fintype.card (lpfRationalCenters Q) : Real) *
      (4 * (Q : Real) ^ 2) <= (n : Real) + 4 * (Q : Real) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hCard (by positivity : 0 <= 4 * (Q : Real) ^ 2)
    nlinarith only [h]
  have hPositive := hamiltonian_physical_frame_norm_square n (hamiltonianRationalCenter R Q)
    (4 * (Q : Real) ^ 2) (by positivity)
    (hamiltonian_rational_center_kernel n Q hQ hRange hDiv)
  have hNegative := hamiltonian_physical_frame_norm_square n
    (fun u => -hamiltonianRationalCenter R Q u) (4 * (Q : Real) ^ 2) (by positivity) (by
      intro u v huv
      have hArg : -hamiltonianRationalCenter R Q v - (-hamiltonianRationalCenter R Q u) =
          -(hamiltonianRationalCenter R Q v - hamiltonianRationalCenter R Q u) := by ring
      rw [hArg, lpfIntervalFrequencyKernel_norm_neg]
      exact hamiltonian_rational_center_kernel n Q hQ hRange hDiv u v huv)
  exact And.intro (hPositive.trans hScale) (hNegative.trans hScale)

theorem hamiltonian_rational_rest_operator_norm {n R : Nat} [NeZero n] [NeZero R]
    (Q : Nat) (hQ : 0 < Q) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R) :
    norm (hamiltonianRationalOperator n R Q (hamiltonianRationalRestCoefficient Q)) <=
      (1 / 2 : Real) + 2 * (Q : Real) ^ 4 / (n : Real) := by
  let A := hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R Q u)
  let B := hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R Q)
  let w := hamiltonianRationalRestCoefficient Q
  let S : Real := (n : Real) + 4 * (Q : Real) ^ 4
  have hFrames := hamiltonian_rational_frame_norms n Q hQ hRange hDiv
  have hProduct : norm A * norm B <= S := by
    have hPositive := hFrames.1
    have hNegative := hFrames.2
    change norm B * norm B <= S at hPositive
    change norm A * norm A <= S at hNegative
    nlinarith only [hPositive, hNegative, sq_nonneg (norm A - norm B)]
  have hDiag : norm (Matrix.diagonal w) <= (1 / 2 : Real) := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)).mpr
      (hamiltonian_rational_rest_coefficient_half Q)
  have hFirst := Matrix.l2_opNorm_mul A (Matrix.diagonal w)
  have hSecond := Matrix.l2_opNorm_mul (A * Matrix.diagonal w) B.conjTranspose
  rw [Matrix.l2_opNorm_conjTranspose] at hSecond
  have hAll : norm ((A * Matrix.diagonal w) * B.conjTranspose) <= (1 / 2 : Real) * S := by
    calc
      _ <= norm (A * Matrix.diagonal w) * norm B := hSecond
      _ <= (norm A * norm (Matrix.diagonal w)) * norm B :=
        mul_le_mul_of_nonneg_right hFirst (norm_nonneg B)
      _ <= (norm A * (1 / 2 : Real)) * norm B := by gcongr
      _ <= (1 / 2 : Real) * S := by nlinarith only [hProduct]
  have hn : (0 : Real) < (n : Real) := by exact_mod_cast (NeZero.pos n)
  unfold hamiltonianRationalOperator
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  change Inv.inv (n : Real) * norm ((A * Matrix.diagonal w) * B.conjTranspose) <= _
  calc
    _ <= Inv.inv (n : Real) * ((1 / 2 : Real) * S) :=
      mul_le_mul_of_nonneg_left hAll (by positivity)
    _ = _ := by dsimp [S]; field_simp; ring

theorem hamiltonian_rational_two_mode_error {n R : Nat} [NeZero n] [NeZero R]
    (Q : Nat) (hQ : 0 < Q) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R) :
    norm (hamiltonianRationalSumMatrix n R Q -
      hamiltonianRationalOperator n R Q (hamiltonianRationalLowCoefficient Q)) <=
        (1 / 2 : Real) + 2 * (Q : Real) ^ 4 / (n : Real) := by
  rw [hamiltonian_rational_low_rest_split]
  simpa only [add_sub_cancel_left] using hamiltonian_rational_rest_operator_norm Q hQ hRange hDiv

end PrimeFactorOscillations.LPF
