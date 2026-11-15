/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianComplementaryPermanentRatio
import PrimeFactorOscillations.Helpers.HamiltonianSignedMinorResidual
import PrimeFactorOscillations.Helpers.HamiltonianTiltedMinorMass

/-! # Exponential tilting of the full retained large-support packet

Only the explicitly retained tail is estimated here. The signed
constant and full first-order terms have separate exact readouts.
Every rank weight and both independent supports are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianMinorTailPacket (T : Matrix Iota Iota Real)
    (E : Finset Iota -> Finset Iota -> Real) (R : Nat) : Real :=
  hamiltonianMinorResidualPacket T (fun S U => if R < U.card then E S U else 0)

theorem hamiltonian_minor_tail_tilt_bound
    (T : Matrix Iota Iota Real) (E : Finset Iota -> Finset Iota -> Real)
    (R : Nat) (C s t : Real) (hC : 0 <= C) (hs : 0 <= s) (ht : 1 <= t)
    (hError : forall S U, Membership.mem (Finset.univ.powersetCard U.card) S ->
      R < U.card -> abs (E S U) <= C * s ^ U.card) :
    t ^ R * abs (hamiltonianMinorTailPacket T E R) <=
      C * hamiltonianTiltedMinorMass T (s * t) := by
  let mask := fun S U : Finset Iota => if R < U.card then E S U else 0
  let inner := fun U : Finset Iota =>
    (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2 * mask S U)
  have ht0 : 0 <= t := le_trans (by norm_num) ht
  have hTR : 0 <= t ^ R := pow_nonneg ht0 R
  have hST : 0 <= s * t := mul_nonneg hs ht0
  have hPowerOne (k : Nat) : 1 <= t ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have h := mul_le_mul_of_nonneg_left ht (le_trans (by norm_num) ih)
      exact le_trans ih (by simpa only [mul_one] using h)
  have hPowerLe (r : Nat) (hR : R <= r) : t ^ R <= t ^ r := by
    have hSplit : r = R + (r - R) := by omega
    have h := mul_le_mul_of_nonneg_left (hPowerOne (r - R)) hTR
    rw [hSplit, pow_add]
    simpa only [mul_one] using h
  have hPoint (S U : Finset Iota)
      (hS : Membership.mem (Finset.univ.powersetCard U.card) S) :
      t ^ R * abs (mask S U) <= C * (s * t) ^ U.card := by
    dsimp only [mask]
    by_cases hR : R < U.card
    case pos =>
      rw [if_pos hR]
      have h1 := mul_le_mul_of_nonneg_left (hError S U hS hR) hTR
      have h2 := mul_le_mul_of_nonneg_right (hPowerLe U.card (Nat.le_of_lt hR))
        (mul_nonneg hC (pow_nonneg hs U.card))
      calc
        _ <= t ^ R * (C * s ^ U.card) := h1
        _ <= (C * s ^ U.card) * t ^ U.card := by nlinarith only [h2]
        _ = _ := by rw [mul_pow]; ring
    case neg =>
      rw [if_neg hR, abs_zero, mul_zero]
      exact mul_nonneg hC (pow_nonneg hST U.card)
  have hInner (U : Finset Iota) :
      t ^ R * abs (inner U) <= C * (s * t) ^ U.card *
        (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2) := by
    calc
      _ <= t ^ R * (Finset.univ.powersetCard U.card).sum
          (fun S => abs (rectangularMinorDet T S U ^ 2 * mask S U)) :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hTR
      _ = (Finset.univ.powersetCard U.card).sum
          (fun S => rectangularMinorDet T S U ^ 2 * (t ^ R * abs (mask S U))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        ring
      _ <= (Finset.univ.powersetCard U.card).sum
          (fun S => rectangularMinorDet T S U ^ 2 * (C * (s * t) ^ U.card)) := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_left (hPoint S U hS) (sq_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
  change t ^ R * abs (-Finset.univ.sum (fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) * inner U)) <= _
  rw [abs_neg]
  calc
    _ <= t ^ R * Finset.univ.sum (fun U : Finset Iota =>
        abs ((-1 : Real) ^ U.card * (U.card : Real) * inner U)) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hTR
    _ = Finset.univ.sum (fun U : Finset Iota => (U.card : Real) *
        (t ^ R * abs (inner U))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      have hCard : (0 : Real) <= (U.card : Real) := Nat.cast_nonneg U.card
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hCard]
      ring
    _ <= Finset.univ.sum (fun U : Finset Iota => (U.card : Real) *
        (C * (s * t) ^ U.card *
          (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2))) :=
      Finset.sum_le_sum (fun U _ => mul_le_mul_of_nonneg_left (hInner U) (Nat.cast_nonneg U.card))
    _ = _ := by
      unfold hamiltonianTiltedMinorMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      ring

theorem stochastic_minor_tail_tilt_bound
    (T : Matrix Iota Iota Real) (E : Finset Iota -> Finset Iota -> Real)
    (R : Nat) (q a C s t : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hC : 0 <= C) (hs : 0 <= s) (ht : 1 <= t)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hError : forall S U, Membership.mem (Finset.univ.powersetCard U.card) S ->
      R < U.card -> abs (E S U) <= C * s ^ U.card) :
    t ^ R * abs (hamiltonianMinorTailPacket T E R) <=
      C * (s * t) * a * (1 + s * t) * Real.exp ((s * t) * (a - 1)) := by
  have ht0 : 0 <= t := le_trans (by norm_num) ht
  calc
    _ <= C * hamiltonianTiltedMinorMass T (s * t) :=
      hamiltonian_minor_tail_tilt_bound T E R C s t hC hs ht hError
    _ <= C * ((s * t) * a * (1 + s * t) * Real.exp ((s * t) * (a - 1))) :=
      mul_le_mul_of_nonneg_left
        (stochastic_tilted_minor_mass_bound T q a (s * t) hq ha
          (mul_nonneg hs ht0) hRow hCol hNonneg hUpper) hC
    _ = _ := by ring

end PrimeFactorOscillations
