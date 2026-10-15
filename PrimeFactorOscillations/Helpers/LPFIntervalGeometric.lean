/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFGridPhase

/-!
# Exact geometric cancellation of the interval kernel

The shifted interval kernel factors into a unit phase and a geometric sum.
Multiplying by 1 minus the root of unity telescopes to two endpoints, so
norm(1-psi(k))*norm(V(k)) <= 2. This includes k=0 without division. Jordan's
inequality gives norm(V(k)) <= N/(2*k) when 0<k and 2*k<=N. The positive
tail energy is at most N^2/(4*W) for W>=1, and the negative kernel is the
complex conjugate. The full inverse tail still needs the cyclic covering.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_geometric_telescoping (r : Complex) (L : Nat) :
    (1 - r) * Finset.sum (Finset.range L) (fun i => r ^ i) = 1 - r ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem lpf_unit_geometric_sum_scaled_bound (r : Complex) (hr : norm r = 1) (L : Nat) :
    norm (1 - r) * norm (Finset.sum (Finset.range L) (fun i => r ^ i)) <= 2 := by
  rw [<- norm_mul, lpf_geometric_telescoping]
  have h := norm_sub_le (1 : Complex) (r ^ L)
  simpa only [norm_one, norm_pow, hr, one_pow, one_add_one_eq_two] using h

theorem lpfGridIntervalKernel_geometric {N : Nat} [NeZero N] (s L : Nat) (k : Int) :
    lpfGridIntervalKernel N s L k =
      (ZMod.stdAddChar (N := N) (k : ZMod N)) ^ (s + 1) *
        Finset.sum (Finset.range L) (fun i => (ZMod.stdAddChar (N := N) (k : ZMod N)) ^ i) := by
  unfold lpfGridIntervalKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [<- pow_add, <- AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem lpfGridIntervalKernel_scaled_bound {N : Nat} [NeZero N] (s L : Nat) (k : Int) :
    norm (1 - ZMod.stdAddChar (N := N) (k : ZMod N)) * norm (lpfGridIntervalKernel N s L k) <= 2 := by
  have hr : norm (ZMod.stdAddChar (N := N) (k : ZMod N)) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [lpfGridIntervalKernel_geometric, norm_mul, norm_pow, hr, one_pow, one_mul]
  exact lpf_unit_geometric_sum_scaled_bound _ hr L

theorem lpf_stdAddChar_nat_exp {N : Nat} [NeZero N] (k : Nat) :
    ZMod.stdAddChar (N := N) (k : ZMod N) =
      Complex.exp (Complex.I * ((2 * Real.pi * (k : Real) / (N : Real) : Real) : Complex)) := by
  have h := ZMod.stdAddChar_coe (N := N) (k : Int)
  simp only [Int.cast_natCast] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem lpf_root_distance_lower_bound {N : Nat} [NeZero N] (k : Nat) (hHalf : 2 * k <= N) :
    4 * (k : Real) / (N : Real) <= norm (1 - ZMod.stdAddChar (N := N) (k : ZMod N)) := by
  have hN : (0 : Real) < (N : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hTwo : 2 * (k : Real) <= (N : Real) := by exact_mod_cast hHalf
  let x : Real := Real.pi * (k : Real) / (N : Real)
  have hX : 0 <= x := by dsimp [x]; positivity
  have hUpper : x <= Real.pi / 2 := by
    have hHalfR : (k : Real) <= (N : Real) / 2 := by linarith
    have hRatio := div_le_div_of_nonneg_right hHalfR hN.le
    have hCancel : ((N : Real) / 2) / (N : Real) = (1 / 2 : Real) := by field_simp
    rw [hCancel] at hRatio
    calc
      x = Real.pi * ((k : Real) / (N : Real)) := by dsimp [x]; ring
      _ <= Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hRatio Real.pi_pos.le
      _ = _ := by ring
  have hNorm : norm (1 - ZMod.stdAddChar (N := N) (k : ZMod N)) = 2 * abs (Real.sin x) := by
    rw [lpf_stdAddChar_nat_exp, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
    have hAngle : (2 * Real.pi * (k : Real) / (N : Real)) / 2 = x := by dsimp [x]; ring
    simp only [hAngle, Real.norm_eq_abs, abs_mul]
    norm_num
  calc
    _ = 2 * (2 / Real.pi * x) := by dsimp [x]; field_simp; ring
    _ <= 2 * Real.sin x := mul_le_mul_of_nonneg_left (Real.mul_le_sin hX hUpper) (by norm_num)
    _ <= 2 * abs (Real.sin x) := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ = _ := hNorm.symm

theorem norm_lpfGridIntervalKernel_le_inverse_frequency {N : Nat} [NeZero N]
    (s L k : Nat) (hk : 0 < k) (hHalf : 2 * k <= N) :
    norm (lpfGridIntervalKernel N s L (k : Int)) <= (N : Real) / (2 * (k : Real)) := by
  have hN : (0 : Real) < (N : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hkR : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hk
  have hScaled := lpfGridIntervalKernel_scaled_bound (N := N) s L (k : Int)
  simp only [Int.cast_natCast] at hScaled
  have hStep := (mul_le_mul_of_nonneg_right (lpf_root_distance_lower_bound (N := N) k hHalf)
    (norm_nonneg (lpfGridIntervalKernel N s L (k : Int)))).trans hScaled
  have hMul : 4 * (k : Real) * norm (lpfGridIntervalKernel N s L (k : Int)) <= 2 * (N : Real) := by
    have h := mul_le_mul_of_nonneg_right hStep hN.le
    have hCancel : (4 * (k : Real) / (N : Real)) *
        norm (lpfGridIntervalKernel N s L (k : Int)) * (N : Real) =
          4 * (k : Real) * norm (lpfGridIntervalKernel N s L (k : Int)) := by field_simp
    rw [hCancel] at h
    exact h
  have hTwoMul : norm (lpfGridIntervalKernel N s L (k : Int)) * (2 * (k : Real)) <= (N : Real) := by nlinarith
  have hDiv := div_le_div_of_nonneg_right hTwoMul (by positivity : (0 : Real) <= 2 * (k : Real))
  have hCancel : (norm (lpfGridIntervalKernel N s L (k : Int)) * (2 * (k : Real))) /
      (2 * (k : Real)) = norm (lpfGridIntervalKernel N s L (k : Int)) := by field_simp
  rw [hCancel] at hDiv
  exact hDiv

theorem lpf_inverse_square_step (x : Real) (hx : 1 < x) :
    1 / x ^ 2 <= 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  calc
    _ <= 1 / (x * (x - 1)) := one_div_le_one_div_of_le (mul_pos hx0 hxm) (by nlinarith)
    _ = _ := by field_simp; ring

theorem lpf_inverse_square_range_tail (W L : Nat) (hW : 1 <= W) :
    Finset.sum (Finset.range L) (fun i => 1 / ((W + 1 + i : Nat) : Real) ^ 2) <=
      1 / (W : Real) - 1 / ((W + L : Nat) : Real) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hStep := lpf_inverse_square_step ((W + 1 + L : Nat) : Real)
      (by exact_mod_cast (show 1 < W + 1 + L by omega))
    have hPrev : ((W + 1 + L : Nat) : Real) - 1 = ((W + L : Nat) : Real) := by push_cast; ring
    have hNext : W + 1 + L = W + (L + 1) := by omega
    rw [hPrev, hNext] at hStep
    rw [hNext]
    calc
      _ <= (1 / (W : Real) - 1 / ((W + L : Nat) : Real)) +
          (1 / ((W + L : Nat) : Real) - 1 / ((W + (L + 1) : Nat) : Real)) := add_le_add ih hStep
      _ = _ := by ring

theorem lpf_inverse_square_Ioc_tail (W Q : Nat) (hW : 1 <= W) :
    Finset.sum (Finset.Ioc W Q) (fun k => 1 / (k : Real) ^ 2) <= 1 / (W : Real) := by
  have hMap : Finset.sum (Finset.range (Q - W)) (fun i => 1 / ((W + 1 + i : Nat) : Real) ^ 2) =
      Finset.sum (Finset.Ioc W Q) (fun k => 1 / (k : Real) ^ 2) := by
    apply Finset.sum_bij (fun i _ => W + 1 + i)
    . intro i hi
      apply Finset.mem_Ioc.mpr
      have h := Finset.mem_range.mp hi
      omega
    . intro i hi j hj hEq
      exact Nat.add_left_cancel hEq
    . intro k hk
      have h := Finset.mem_Ioc.mp hk
      refine Exists.intro (k - W - 1) (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr; omega
      . omega
    . intro i hi
      rfl
  rw [<- hMap]
  exact (lpf_inverse_square_range_tail W (Q - W) hW).trans
    (sub_le_self _ (by positivity))

theorem lpfGridIntervalKernel_positive_tail_energy {N : Nat} [NeZero N]
    (s L W : Nat) (hW : 1 <= W) :
    Finset.sum (Finset.Ioc W (N / 2)) (fun k => norm (lpfGridIntervalKernel N s L (k : Int)) ^ 2) <=
      (N : Real) ^ 2 / (4 * (W : Real)) := by
  have hPoint : forall k, Membership.mem (Finset.Ioc W (N / 2)) k ->
      norm (lpfGridIntervalKernel N s L (k : Int)) ^ 2 <=
        ((N : Real) ^ 2 / 4) * (1 / (k : Real) ^ 2) := by
    intro k hk
    have h := Finset.mem_Ioc.mp hk
    have hkPos : 0 < k := by omega
    have hHalf : 2 * k <= N := by omega
    have hNorm := norm_lpfGridIntervalKernel_le_inverse_frequency s L k hkPos hHalf
    calc
      _ <= ((N : Real) / (2 * (k : Real))) ^ 2 := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ <= Finset.sum (Finset.Ioc W (N / 2)) (fun k => ((N : Real) ^ 2 / 4) * (1 / (k : Real) ^ 2)) :=
      Finset.sum_le_sum hPoint
    _ = ((N : Real) ^ 2 / 4) * Finset.sum (Finset.Ioc W (N / 2)) (fun k => 1 / (k : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= ((N : Real) ^ 2 / 4) * (1 / (W : Real)) :=
      mul_le_mul_of_nonneg_left (lpf_inverse_square_Ioc_tail W (N / 2) hW) (by positivity)
    _ = _ := by ring

theorem lpf_stdAddChar_neg_star {N : Nat} [NeZero N] (x : ZMod N) :
    ZMod.stdAddChar (N := N) (-x) = star (ZMod.stdAddChar (N := N) x) := by
  have hNorm : norm (ZMod.stdAddChar (N := N) x) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hSq : Complex.normSq (ZMod.stdAddChar (N := N) x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hNorm]
    norm_num
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, hSq]
  simp

theorem lpfGridIntervalKernel_neg_star {N : Nat} [NeZero N] (s L : Nat) (k : Int) :
    lpfGridIntervalKernel N s L (-k) = star (lpfGridIntervalKernel N s L k) := by
  unfold lpfGridIntervalKernel
  change _ = (starRingEnd Complex) (Finset.sum (Finset.range L)
    (fun i => ZMod.stdAddChar (N := N) ((k : ZMod N) * ((s + 1 + i : Nat) : ZMod N))))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : ((-k : Int) : ZMod N) * ((s + 1 + i : Nat) : ZMod N) =
      -((k : ZMod N) * ((s + 1 + i : Nat) : ZMod N)) := by rw [Int.cast_neg]; ring
  rw [h, lpf_stdAddChar_neg_star]
  rfl

theorem norm_lpfGridIntervalKernel_neg {N : Nat} [NeZero N] (s L : Nat) (k : Int) :
    norm (lpfGridIntervalKernel N s L (-k)) = norm (lpfGridIntervalKernel N s L k) := by
  rw [lpfGridIntervalKernel_neg_star, norm_star]

end PrimeFactorOscillations.LPF
