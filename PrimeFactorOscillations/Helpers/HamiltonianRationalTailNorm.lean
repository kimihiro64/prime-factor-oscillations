/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalModelNorm
import PrimeFactorOscillations.Helpers.LPFTotientTail

/-! # Arbitrarily small rational tails with the complete low modes retained

The generic two-frame estimate applies to every signed coefficient function.
The existing quartic totient theorem supplies a fixed denominator cutoff.
This is an operator-tail input for the cycle-packing determinant consumer;
it does not yet assert that the finite-outlier amplification bound is closed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_rational_operator_coefficient_norm
    {n R : Nat} [NeZero n] [NeZero R]
    (Q : Nat) (hQ : 0 < Q) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R)
    (w : lpfRationalCenters Q -> Complex) (eta : Real) (hEta : 0 <= eta)
    (hCoeff : forall u, norm (w u) <= eta) :
    norm (hamiltonianRationalOperator n R Q w) <=
      eta * (1 + 4 * (Q : Real) ^ 4 / (n : Real)) := by
  let A := hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R Q u)
  let B := hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R Q)
  let S : Real := (n : Real) + 4 * (Q : Real) ^ 4
  have hFrames := hamiltonian_rational_frame_norms n Q hQ hRange hDiv
  have hProduct : norm A * norm B <= S := by
    have hPositive := hFrames.1
    have hNegative := hFrames.2
    change norm B * norm B <= S at hPositive
    change norm A * norm A <= S at hNegative
    nlinarith only [hPositive, hNegative, sq_nonneg (norm A - norm B)]
  have hDiag : norm (Matrix.diagonal w) <= eta := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hEta).mpr hCoeff
  have hFirst := Matrix.l2_opNorm_mul A (Matrix.diagonal w)
  have hSecond := Matrix.l2_opNorm_mul (A * Matrix.diagonal w) B.conjTranspose
  rw [Matrix.l2_opNorm_conjTranspose] at hSecond
  have hAll : norm ((A * Matrix.diagonal w) * B.conjTranspose) <= eta * S := by
    calc
      _ <= norm (A * Matrix.diagonal w) * norm B := hSecond
      _ <= (norm A * norm (Matrix.diagonal w)) * norm B :=
        mul_le_mul_of_nonneg_right hFirst (norm_nonneg B)
      _ <= (norm A * eta) * norm B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDiag (norm_nonneg A)) (norm_nonneg B)
      _ <= eta * S := by
        have h := mul_le_mul_of_nonneg_left hProduct hEta
        nlinarith only [h]
  have hn : 0 < (n : Real) := Nat.cast_pos.mpr (NeZero.pos n)
  unfold hamiltonianRationalOperator
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  change Inv.inv (n : Real) * norm ((A * Matrix.diagonal w) * B.conjTranspose) <= _
  calc
    _ <= Inv.inv (n : Real) * (eta * S) :=
      mul_le_mul_of_nonneg_left hAll (by positivity)
    _ = _ := by dsimp only [S]; field_simp [ne_of_gt hn] <;> ring

theorem hamiltonian_totient_cutoff (K q : Nat) (hK : 0 < K) (hHigh : 27 * K ^ 4 < q) :
    K < q.totient := by
  by_contra h
  have hp : q.totient <= K := by omega
  have hp2 := Nat.mul_le_mul hp hp
  have hp4 := Nat.mul_le_mul hp2 hp2
  have hq : 1 <= q := by omega
  have hq2 := Nat.mul_le_mul hq hq
  have hq3 := Nat.mul_le_mul_left q hq2
  have hLower := lpf_totient_quartic_lower_bound q
  nlinarith only [hHigh, hp4, hq3, hLower]

theorem hamiltonian_rational_coefficient_after_cutoff
    (K q : Nat) (hK : 0 < K) (hHigh : 27 * K ^ 4 < q) :
    norm (lpfRationalCoefficient q) <= 1 / (K : Real) := by
  have hq : 0 < q := by omega
  have hPhi := hamiltonian_totient_cutoff K q hK hHigh
  have hKR : 0 < (K : Real) := Nat.cast_pos.mpr hK
  have hCompare : (K : Real) <= (q.totient : Real) := Nat.cast_le.mpr hPhi.le
  exact (norm_lpfRationalCoefficient_le q hq).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1) hKR hCompare)

def hamiltonianRationalCutoffLow (Q K : Nat) (u : lpfRationalCenters Q) : Complex :=
  if u.1.val + 1 <= 27 * K ^ 4 then lpfRationalCoefficient (u.1.val + 1) else 0

def hamiltonianRationalCutoffRest (Q K : Nat) (u : lpfRationalCenters Q) : Complex :=
  if u.1.val + 1 <= 27 * K ^ 4 then 0 else lpfRationalCoefficient (u.1.val + 1)

theorem hamiltonian_rational_cutoff_split {R : Nat} [NeZero R] (n Q K : Nat) :
    hamiltonianRationalSumMatrix n R Q =
      hamiltonianRationalOperator n R Q (hamiltonianRationalCutoffLow Q K) +
        hamiltonianRationalOperator n R Q (hamiltonianRationalCutoffRest Q K) := by
  rw [<- hamiltonian_rational_operator_add, hamiltonian_rational_sum_operator]
  congr 1
  funext u
  unfold hamiltonianRationalCutoffLow hamiltonianRationalCutoffRest
  split <;> simp

theorem hamiltonian_rational_cutoff_operator_error
    {n R : Nat} [NeZero n] [NeZero R]
    (Q K : Nat) (hQ : 0 < Q) (hK : 0 < K) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R) :
    norm (hamiltonianRationalSumMatrix n R Q -
      hamiltonianRationalOperator n R Q (hamiltonianRationalCutoffLow Q K)) <=
      (1 / (K : Real)) * (1 + 4 * (Q : Real) ^ 4 / (n : Real)) := by
  have hCoeff : forall u : lpfRationalCenters Q,
      norm (hamiltonianRationalCutoffRest Q K u) <= 1 / (K : Real) := by
    intro u
    unfold hamiltonianRationalCutoffRest
    split
    next h => simp only [norm_zero]; positivity
    next h =>
      exact hamiltonian_rational_coefficient_after_cutoff K (u.1.val + 1) hK (by omega)
  rw [hamiltonian_rational_cutoff_split (R := R) n Q K]
  simpa only [add_sub_cancel_left] using
    hamiltonian_rational_operator_coefficient_norm Q hQ hRange hDiv
      (hamiltonianRationalCutoffRest Q K) (1 / (K : Real)) (by positivity) hCoeff

end PrimeFactorOscillations.LPF
