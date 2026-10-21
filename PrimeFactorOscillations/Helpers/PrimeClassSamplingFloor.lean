/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform floor error in the full prime-component sampling law

The signed floor discrepancy is retained as an exact residue sum. Only this
explicit sampling remainder is then estimated in absolute value. The estimate
is uniform in every finite divisor support and charges its full weighted mass.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def floorSamplingError (N q : Nat) : Real :=
  1 / (q : Real) - (N / q : Nat) / (N : Real)

theorem floorSamplingError_eq_residue (N q : Nat) (hN : 0 < N) (hq : 0 < q) :
    floorSamplingError N q =
      (N % q : Nat) / ((N : Real) * (q : Real)) := by
  have hNreal : Not ((N : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hqreal : Not ((q : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hdivision : ((N % q : Nat) : Real) +
      (q : Real) * ((N / q : Nat) : Real) = (N : Real) := by
    exact_mod_cast Nat.mod_add_div N q
  unfold floorSamplingError
  field_simp
  nlinarith only [hdivision]

theorem floorSamplingError_nonneg (N q : Nat) (hN : 0 < N) (hq : 0 < q) :
    0 <= floorSamplingError N q := by
  rw [floorSamplingError_eq_residue N q hN hq]
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem floorSamplingError_le_inv_sample (N q : Nat) (hN : 0 < N) (hq : 0 < q) :
    floorSamplingError N q <= 1 / (N : Real) := by
  have hNreal : Not ((N : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hqreal : Not ((q : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  rw [floorSamplingError_eq_residue N q hN hq]
  calc
    ((N % q : Nat) : Real) / ((N : Real) * (q : Real)) <=
        (q : Real) / ((N : Real) * (q : Real)) :=
      div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (Nat.le_of_lt (Nat.mod_lt N hq)))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = 1 / (N : Real) := by field_simp

theorem floorSamplingError_le_inv_divisor (N q : Nat) :
    floorSamplingError N q <= 1 / (q : Real) := by
  exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem min_le_geometric_interpolation
    (a b sigma : Real) (ha : 0 < a) (hb : 0 < b)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    min a b <= a ^ (1 - sigma) * b ^ sigma := by
  by_cases hab : a <= b
  case pos =>
    rw [min_eq_left hab]
    calc
      a = a ^ (1 - sigma) * a ^ sigma := by
        rw [<- Real.rpow_add ha, sub_add_cancel, Real.rpow_one]
      _ <= a ^ (1 - sigma) * b ^ sigma :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (le_of_lt ha) hab hs0)
          (le_of_lt (Real.rpow_pos_of_pos ha _))
  case neg =>
    have hba : b <= a := le_of_not_ge hab
    rw [min_eq_right hba]
    calc
      b = b ^ (1 - sigma) * b ^ sigma := by
        rw [<- Real.rpow_add hb, sub_add_cancel, Real.rpow_one]
      _ <= a ^ (1 - sigma) * b ^ sigma :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt hb) hba (sub_nonneg.mpr hs1))
          (le_of_lt (Real.rpow_pos_of_pos hb _))

theorem floorSamplingError_le_rpow
    (N q : Nat) (hN : 0 < N) (hq : 0 < q) (sigma : Real)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    floorSamplingError N q <=
      (N : Real) ^ (sigma - 1) * (q : Real) ^ (-sigma) := by
  have hNpos : (0 : Real) < N := Nat.cast_pos.mpr hN
  have hqpos : (0 : Real) < q := Nat.cast_pos.mpr hq
  have hbound := (le_min
    (floorSamplingError_le_inv_sample N q hN hq)
    (floorSamplingError_le_inv_divisor N q)).trans
    (min_le_geometric_interpolation (1 / (N : Real)) (1 / (q : Real))
      sigma (one_div_pos.mpr hNpos) (one_div_pos.mpr hqpos) hs0 hs1)
  have hnormal :
      (1 / (N : Real)) ^ (1 - sigma) * (1 / (q : Real)) ^ sigma =
        (N : Real) ^ (sigma - 1) * (q : Real) ^ (-sigma) := by
    simp only [one_div, Real.inv_rpow (le_of_lt hNpos),
      Real.inv_rpow (le_of_lt hqpos),
      <- Real.rpow_neg (le_of_lt hNpos), <- Real.rpow_neg (le_of_lt hqpos)]
    congr 2
    ring
  rw [hnormal] at hbound
  exact hbound

noncomputable def signedFloorDiscrepancy
    (N : Nat) (s : Finset Nat) (weight : Nat -> Real) : Real :=
  s.sum (fun q => weight q * (((N / q : Nat) : Real) / (N : Real) - 1 / (q : Real)))

theorem signedFloorDiscrepancy_eq_residue_sum
    (N : Nat) (s : Finset Nat) (weight : Nat -> Real)
    (hN : 0 < N) (hq : forall q, Membership.mem s q -> 0 < q) :
    signedFloorDiscrepancy N s weight =
      -(s.sum (fun q => weight q *
        (((N % q : Nat) : Real) / ((N : Real) * (q : Real))))) := by
  unfold signedFloorDiscrepancy
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hmem
  rw [<- floorSamplingError_eq_residue N q hN (hq q hmem)]
  unfold floorSamplingError
  ring

theorem abs_signedFloorDiscrepancy_le
    (N : Nat) (s : Finset Nat) (weight : Nat -> Real)
    (hN : 0 < N) (hq : forall q, Membership.mem s q -> 0 < q)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    abs (signedFloorDiscrepancy N s weight) <=
      (N : Real) ^ (sigma - 1) *
        s.sum (fun q => abs (weight q) * (q : Real) ^ (-sigma)) := by
  unfold signedFloorDiscrepancy
  calc
    abs (s.sum (fun q => weight q *
        (((N / q : Nat) : Real) / (N : Real) - 1 / (q : Real)))) <=
        s.sum (fun q => abs (weight q *
          (((N / q : Nat) : Real) / (N : Real) - 1 / (q : Real)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = s.sum (fun q => abs (weight q) * floorSamplingError N q) := by
      apply Finset.sum_congr rfl
      intro q hmem
      have hneg : ((N / q : Nat) : Real) / (N : Real) - 1 / (q : Real) =
          -floorSamplingError N q := by unfold floorSamplingError; ring
      rw [abs_mul, hneg, abs_neg,
        abs_of_nonneg (floorSamplingError_nonneg N q hN (hq q hmem))]
    _ <= s.sum (fun q => abs (weight q) *
        ((N : Real) ^ (sigma - 1) * (q : Real) ^ (-sigma))) := by
      apply Finset.sum_le_sum
      intro q hmem
      exact mul_le_mul_of_nonneg_left
        (floorSamplingError_le_rpow N q hN (hq q hmem) sigma hs0 hs1)
        (abs_nonneg _)
    _ = (N : Real) ^ (sigma - 1) *
        s.sum (fun q => abs (weight q) * (q : Real) ^ (-sigma)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hmem
      ring

end PrimeFactorOscillations.PrimeClassSampling
