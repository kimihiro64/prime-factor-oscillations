/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Scalar power-mass interpolation for the trace-power Hessian -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota]

theorem hamiltonian_concave_power_mass
    (s : Finset Iota) (a : Iota -> Real) (ha : forall i, Membership.mem s i -> 0 <= a i)
    (q : Real) (hq0 : 0 <= q) (hq1 : q <= 1) :
    s.sum (fun i => a i ^ q) <= (s.card : Real) ^ (1 - q) * (s.sum a) ^ q := by
  by_cases hq : q = 0
  case pos =>
    subst q
    simp only [Real.rpow_zero, sub_zero, Real.rpow_one, Finset.sum_const,
      nsmul_eq_mul, mul_one, le_refl]
  have hqPos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
  have hInv : 0 <= 1 / q := (one_div_pos.mpr hqPos).le
  have hProd : q * (1 / q) = 1 := by field_simp
  have hProd' : (1 / q) * q = 1 := by rw [mul_comm]; exact hProd
  have hInvOne : 1 <= 1 / q := by
    have h := mul_le_mul_of_nonneg_right hq1 hInv
    nlinarith only [h, hProd]
  have hPower := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := fun i => a i ^ q) hInvOne
    (fun i hi => Real.rpow_nonneg (ha i hi) q)
  have hEntry : s.sum (fun i => (a i ^ q) ^ (1 / q)) = s.sum a := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [<- Real.rpow_mul (ha i hi), hProd, Real.rpow_one]
  rw [hEntry] at hPower
  have hRaised := Real.rpow_le_rpow
    (Real.rpow_nonneg (Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (ha i hi) q)) _)
    hPower hq0
  have hSum : 0 <= s.sum a := Finset.sum_nonneg ha
  have hCard : (0 : Real) <= s.card := Nat.cast_nonneg _
  have hLeft : ((s.sum (fun i => a i ^ q)) ^ (1 / q)) ^ q =
      s.sum (fun i => a i ^ q) := by
    rw [<- Real.rpow_mul
      (Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (ha i hi) q)),
      hProd', Real.rpow_one]
  have hExp : (1 / q - 1) * q = 1 - q := by nlinarith only [hProd']
  rw [hLeft, Real.mul_rpow (Real.rpow_nonneg hCard _) hSum,
    <- Real.rpow_mul hCard, hExp] at hRaised
  exact hRaised

theorem hamiltonian_trace_power_mass_interpolation
    (s : Finset Iota) (a : Iota -> Real) (p : Nat) (hp : 2 <= p) :
    s.sum (fun i => abs (a i) ^ (p - 2)) <=
      (s.card : Real) ^ (2 / (p : Real)) *
        (s.sum (fun i => abs (a i) ^ p)) ^
          (((p : Real) - 2) / (p : Real)) := by
  have hpPos : (0 : Real) < p := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hp)
  have hpNe : Not ((p : Real) = 0) := ne_of_gt hpPos
  have hpTwo : (2 : Real) <= p := by exact_mod_cast hp
  let q : Real := ((p : Real) - 2) / (p : Real)
  have hq0 : 0 <= q := div_nonneg (sub_nonneg.mpr hpTwo) hpPos.le
  have hq1 : q <= 1 := by
    dsimp [q]
    apply (div_le_one hpPos).mpr
    linarith
  have h := hamiltonian_concave_power_mass s (fun i => abs (a i) ^ p)
    (fun i _ => pow_nonneg (abs_nonneg _) _) q hq0 hq1
  have hSub : ((p - 2 : Nat) : Real) = (p : Real) - 2 := by
    rw [Nat.cast_sub hp]
    norm_num
  have hExp : (p : Real) * q = (p : Real) - 2 := by
    dsimp [q]
    field_simp
  have hEntry : s.sum (fun i => ((abs (a i)) ^ p : Real) ^ q) =
      s.sum (fun i => abs (a i) ^ (p - 2)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (abs_nonneg _),
      hExp, <- hSub, Real.rpow_natCast]
  have hCardExp : 1 - q = 2 / (p : Real) := by
    dsimp [q]
    field_simp
    ring
  rw [hEntry, hCardExp] at h
  exact h

end PrimeFactorOscillations
