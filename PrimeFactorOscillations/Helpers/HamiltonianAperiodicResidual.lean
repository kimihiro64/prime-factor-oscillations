/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicLiu
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicMinorTail

/-! # The complete separated aperiodic ratio error

The exact signed signal is evaluated first. Only the full remaining
ratio-minus-one sum is split at the cutoff. Both the low allowance
and the complete high-support subtraction remain in the final bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_nonnegative_exponential_ratio_error
    (v K r : Real) (hv : 0 <= v) (hr : 0 <= r)
    (hUpper : v <= K * Real.exp r) :
    abs (v - 1) <= (K + 1) * Real.exp r := by
  have hExp : 1 <= Real.exp r := Real.one_le_exp hr
  have hAbs : abs (v - 1) <= v + 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hv]
  nlinarith only [hAbs, hUpper, hExp]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem stochastic_aperiodic_error_from_ratio_bounds
    (T : Matrix Iota Iota Real) (q R eps K : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hEps : 0 <= eps)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hLow : forall S : Finset Iota, (S.card : Real) <= R ->
      abs (hamiltonianAperiodicMinorRatio T S - 1) <= eps)
    (hAll : forall S : Finset Iota,
      0 <= hamiltonianAperiodicMinorRatio T S /\
        hamiltonianAperiodicMinorRatio T S <= K * Real.exp (S.card : Real)) :
    abs ((Fintype.card Iota : Real) * hamiltonianCycleSum T / weightedPermutationSum T -
        Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q)) <=
      eps * hamiltonianPrincipalTiltedMass T 1 +
        (K + 1) * (Finset.univ.filter
          (fun S : Finset Iota => R < (S.card : Real))).sum
            (fun S => (S.card : Real) * Real.exp (S.card : Real) *
              abs (principalMinorDet T S)) := by
  let w : Finset Iota -> Real := fun S => (S.card : Real) * abs (principalMinorDet T S)
  have hW (S : Finset Iota) : 0 <= w S :=
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hPoint (S : Finset Iota) :
      w S * abs (hamiltonianAperiodicMinorRatio T S - 1) <=
        eps * w S + (if R < (S.card : Real) then
          (K + 1) * (S.card : Real) * Real.exp (S.card : Real) *
            abs (principalMinorDet T S) else 0) := by
    by_cases hR : R < (S.card : Real)
    case pos =>
      rw [ite_eq_left hR]
      have hErr := hamiltonian_nonnegative_exponential_ratio_error
        (hamiltonianAperiodicMinorRatio T S) K (S.card : Real)
        (hAll S).1 (Nat.cast_nonneg _) (hAll S).2
      have h := mul_le_mul_of_nonneg_left hErr (hW S)
      have hExtra : 0 <= eps * w S := mul_nonneg hEps (hW S)
      dsimp only [w] at h hExtra
      dsimp only [w]
      nlinarith only [h, hExtra]
    case neg =>
      rw [ite_eq_right hR]
      have h := mul_le_mul_of_nonneg_left (hLow S (le_of_not_gt hR)) (hW S)
      nlinarith only [h]
  have hAbsolute (S : Finset Iota) :
      abs ((S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card *
        (hamiltonianAperiodicMinorRatio T S - 1)) =
      w S * abs (hamiltonianAperiodicMinorRatio T S - 1) := by
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= (S.card : Real) from Nat.cast_nonneg S.card), abs_pow,
      abs_neg, abs_one, one_pow, mul_one, w]
  have hLowSum : Finset.univ.sum (fun S : Finset Iota => eps * w S) =
      eps * hamiltonianPrincipalTiltedMass T 1 := by
    unfold hamiltonianPrincipalTiltedMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [hamiltonianPrincipalTiltedMass, one_pow, mul_one, w]
  have hHighSum : Finset.univ.sum (fun S : Finset Iota =>
      if R < (S.card : Real) then
        (K + 1) * (S.card : Real) * Real.exp (S.card : Real) *
          abs (principalMinorDet T S) else 0) =
      (K + 1) * (Finset.univ.filter (fun S : Finset Iota => R < (S.card : Real))).sum
        (fun S => (S.card : Real) * Real.exp (S.card : Real) *
          abs (principalMinorDet T S)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hR : R < (S.card : Real)
    case pos => simp only [ite_eq_left hR]; ring
    case neg => simp only [ite_eq_right hR]
  rw [stochastic_aperiodic_signed_residual T q hq hRow hCol, abs_neg]
  calc
    _ <= Finset.univ.sum (fun S : Finset Iota =>
        abs ((S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card *
          (hamiltonianAperiodicMinorRatio T S - 1))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun S : Finset Iota =>
        w S * abs (hamiltonianAperiodicMinorRatio T S - 1)) :=
      Finset.sum_congr rfl (fun S _ => hAbsolute S)
    _ <= Finset.univ.sum (fun S : Finset Iota =>
        eps * w S + (if R < (S.card : Real) then
          (K + 1) * (S.card : Real) * Real.exp (S.card : Real) *
            abs (principalMinorDet T S) else 0)) :=
      Finset.sum_le_sum (fun S _ => hPoint S)
    _ = _ := by rw [Finset.sum_add_distrib, hLowSum, hHighSum]

theorem stochastic_aperiodic_complete_residual_envelope
    (T : Matrix Iota Iota Real) (q c R eps K : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hc : 0 < c) (hEps : 0 <= eps) (hK : 0 <= K)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hEntry : forall i j, abs (T i j) <= c)
    (hLow : forall S : Finset Iota, (S.card : Real) <= R ->
      abs (hamiltonianAperiodicMinorRatio T S - 1) <= eps)
    (hAll : forall S : Finset Iota,
      0 <= hamiltonianAperiodicMinorRatio T S /\
        hamiltonianAperiodicMinorRatio T S <= K * Real.exp (S.card : Real)) :
    abs ((Fintype.card Iota : Real) * hamiltonianCycleSum T / weightedPermutationSum T -
        Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q)) <=
      eps * (2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2)) +
        (K + 1) * Real.exp (-R) *
          (2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 *
            (Real.exp 2) ^ 2)) := by
  have h := stochastic_aperiodic_error_from_ratio_bounds T q R eps K hq hEps
    hRow hCol hLow hAll
  have hSmall := hamiltonian_principal_tilted_mass_bound T c 1 hc hEntry
  norm_num only [one_pow, mul_one] at hSmall
  have hLarge := hamiltonian_principal_exponential_tail T c R hc hEntry
  calc
    _ <= _ := h
    _ <= eps * (2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2)) +
        (K + 1) * (Real.exp (-R) *
          (2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 *
            (Real.exp 2) ^ 2))) :=
      add_le_add (mul_le_mul_of_nonneg_left hSmall hEps)
        (mul_le_mul_of_nonneg_left hLarge (by linarith only [hK]))
    _ = _ := by ring

end PrimeFactorOscillations
