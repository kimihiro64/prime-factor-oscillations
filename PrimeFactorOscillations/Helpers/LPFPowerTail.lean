/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
The quantitative 3/2-power tail, retaining its moving lower endpoint.
It is used after the exact Ramanujan divisor reindexing, not as a claim
that local independence transfers to generated states.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_inverse_power_step (x : Real) (hx : 1 < x) :
    1 / (x * Real.sqrt x) <=
      2 * (1 / Real.sqrt (x - 1) - 1 / Real.sqrt x) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x - 1)
  have hxPos : 0 < x := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr hxPos
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hA : a ^ 2 = x := Real.sq_sqrt hxPos.le
  have hB : b ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hAb := congrArg (fun z : Real => z * b) hA
  have hBb := congrArg (fun z : Real => z * b) hB
  have hRel : a ^ 2 * b - b ^ 3 = b := by nlinarith only [hAb, hBb]
  have hTriple : 0 <= (a - b) ^ 2 * (2 * a + b) := by positivity
  have hCore : b <= 2 * (a - b) * a ^ 2 := by nlinarith only [hRel, hTriple]
  have hCoreX : b <= 2 * (a - b) * x := by rw [<- hA]; exact hCore
  have hLeft : (1 / (x * a)) * (x * a * b) = b := by
    field_simp [ne_of_gt hxPos, ne_of_gt ha]
  have hRight : 2 * (1 / b - 1 / a) * (x * a * b) = 2 * x * (a - b) := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
  change 1 / (x * a) <= 2 * (1 / b - 1 / a)
  apply (mul_le_mul_iff_of_pos_right (mul_pos (mul_pos hxPos ha) hb)).mp
  rw [hLeft, hRight]
  nlinarith only [hCoreX]

theorem lpf_nat_inverse_power_step (n : Nat) (hn : 2 <= n) :
    1 / (n : Real) ^ (3 / 2 : Real) <=
      2 * (1 / Real.sqrt ((n - 1 : Nat) : Real) - 1 / Real.sqrt (n : Real)) := by
  have hnR : (1 : Real) < (n : Real) := by exact_mod_cast (show 1 < n by omega)
  have hnPos : (0 : Real) < (n : Real) := by linarith
  have hCast : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by
    rw [Nat.cast_sub (show 1 <= n by omega), Nat.cast_one]
  have hPower : (n : Real) ^ (3 / 2 : Real) = (n : Real) * Real.sqrt (n : Real) := by
    rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num, Real.rpow_add hnPos,
      Real.rpow_one, <- Real.sqrt_eq_rpow]
  rw [hCast, hPower]
  exact lpf_inverse_power_step (n : Real) hnR

theorem lpf_inverse_power_range_tail (P L : Nat) (hP : 1 <= P) :
    Finset.sum (Finset.range L) (fun i => 1 / ((P + 1 + i : Nat) : Real) ^ (3 / 2 : Real)) <=
      2 * (1 / Real.sqrt (P : Real) - 1 / Real.sqrt ((P + L : Nat) : Real)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hStep := lpf_nat_inverse_power_step (P + 1 + L) (by omega)
    have hPred : P + 1 + L - 1 = P + L := by omega
    rw [hPred] at hStep
    have hBound := add_le_add ih hStep
    convert hBound using 1 <;> push_cast <;> ring

theorem lpf_inverse_power_range_tail_le (P L : Nat) (hP : 1 <= P) :
    Finset.sum (Finset.range L) (fun i => 1 / ((P + 1 + i : Nat) : Real) ^ (3 / 2 : Real)) <=
      2 / Real.sqrt (P : Real) := by
  have h := lpf_inverse_power_range_tail P L hP
  have hInv : 0 <= 1 / Real.sqrt ((P + L : Nat) : Real) := by positivity
  rw [show 2 / Real.sqrt (P : Real) = 2 * (1 / Real.sqrt (P : Real)) by ring]
  linarith

theorem lpf_inverse_power_positive_range (L : Nat) :
    Finset.sum (Finset.range (L + 1)) (fun i => 1 / ((1 + i : Nat) : Real) ^ (3 / 2 : Real)) <=
      3 - 2 / Real.sqrt ((L + 1 : Nat) : Real) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hStep := lpf_nat_inverse_power_step (L + 2) (by omega)
    have hPred : L + 2 - 1 = L + 1 := by omega
    rw [hPred] at hStep
    have hBound := add_le_add ih hStep
    convert hBound using 1 <;> push_cast <;> ring

theorem lpf_inverse_power_positive_range_le (L : Nat) :
    Finset.sum (Finset.range L) (fun i => 1 / ((1 + i : Nat) : Real) ^ (3 / 2 : Real)) <= 3 := by
  cases L with
  | zero => norm_num
  | succ L =>
    have h := lpf_inverse_power_positive_range L
    have hInv : 0 <= 2 / Real.sqrt ((L + 1 : Nat) : Real) := by positivity
    linarith

theorem lpf_inverse_power_multiples_tail (d P L : Nat) (hd : 1 <= d) (hP : 1 <= P) :
    Finset.sum (Finset.range L) (fun i => (d : Real) /
      ((d * (P / d + 1 + i) : Nat) : Real) ^ (3 / 2 : Real)) <=
      4 / Real.sqrt (P : Real) := by
  let K := P / d
  have hdPos : 0 < d := by omega
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hdPos
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hSD : 0 < Real.sqrt (d : Real) := Real.sqrt_pos.mpr hdR
  have hSP : 0 < Real.sqrt (P : Real) := Real.sqrt_pos.mpr hPR
  have hPower : (d : Real) ^ (3 / 2 : Real) = (d : Real) * Real.sqrt (d : Real) := by
    rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num, Real.rpow_add hdR,
      Real.rpow_one, <- Real.sqrt_eq_rpow]
  have hFactor (i : Nat) : (d : Real) /
      ((d * (K + 1 + i) : Nat) : Real) ^ (3 / 2 : Real) =
      (1 / Real.sqrt (d : Real)) * (1 / ((K + 1 + i : Nat) : Real) ^ (3 / 2 : Real)) := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg (K + 1 + i)), hPower]
    field_simp [ne_of_gt hdR, ne_of_gt hSD]
  change Finset.sum (Finset.range L) (fun i => (d : Real) /
    ((d * (K + 1 + i) : Nat) : Real) ^ (3 / 2 : Real)) <= _
  simp_rw [hFactor]
  rw [<- Finset.mul_sum]
  have hDivMod := Nat.div_add_mod P d
  have hMod := Nat.mod_lt P hdPos
  by_cases hK : K = 0
  . have hPd : P < d := by dsimp [K] at hK; rw [hK] at hDivMod; omega
    have hRoots : Real.sqrt (P : Real) <= Real.sqrt (d : Real) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hPd.le)
    have hInv := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1) hSP hRoots
    have hTotal : Finset.sum (Finset.range L)
        (fun i => 1 / ((K + 1 + i : Nat) : Real) ^ (3 / 2 : Real)) <= 3 := by
      simpa only [hK, Nat.zero_add] using lpf_inverse_power_positive_range_le L
    have hOne := mul_le_mul_of_nonneg_left hTotal (by positivity : 0 <= 1 / Real.sqrt (d : Real))
    have hTwo := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 3)
    calc
      _ <= (1 / Real.sqrt (d : Real)) * 3 := hOne
      _ <= 3 / Real.sqrt (P : Real) := by convert hTwo using 1 <;> ring
      _ <= _ := div_le_div_of_nonneg_right (by norm_num) hSP.le
  . have hK1 : 1 <= K := Nat.pos_of_ne_zero hK
    have hKR : (0 : Real) < (K : Real) := by exact_mod_cast (show 0 < K by omega)
    have hSK : 0 < Real.sqrt (K : Real) := Real.sqrt_pos.mpr hKR
    have hMul : d <= d * K := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hK1
    have hPk : P <= 2 * d * K := by change d * K + P % d = P at hDivMod; nlinarith only [hDivMod, hMod, hMul]
    have hPkR : (P : Real) <= 2 * (d : Real) * (K : Real) := by exact_mod_cast hPk
    have hP4 : (P : Real) <= 4 * ((d : Real) * (K : Real)) := by
      nlinarith only [hPkR, mul_nonneg hdR.le hKR.le]
    have hRoots := Real.sqrt_le_sqrt hP4
    rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 4), Real.sqrt_mul (Nat.cast_nonneg d)] at hRoots
    have hS4 : Real.sqrt (4 : Real) = 2 := by
      rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [hS4] at hRoots
    have hInv : (1 / Real.sqrt (d : Real)) * (2 / Real.sqrt (K : Real)) <=
        4 / Real.sqrt (P : Real) := by
      apply (mul_le_mul_iff_of_pos_right (mul_pos (mul_pos hSD hSK) hSP)).mp
      have hLeft : (1 / Real.sqrt (d : Real)) * (2 / Real.sqrt (K : Real)) *
          (Real.sqrt (d : Real) * Real.sqrt (K : Real) * Real.sqrt (P : Real)) =
          2 * Real.sqrt (P : Real) := by field_simp [ne_of_gt hSD, ne_of_gt hSK]
      have hRight : (4 / Real.sqrt (P : Real)) *
          (Real.sqrt (d : Real) * Real.sqrt (K : Real) * Real.sqrt (P : Real)) =
          4 * Real.sqrt (d : Real) * Real.sqrt (K : Real) := by field_simp [ne_of_gt hSP]
      rw [hLeft, hRight]
      nlinarith only [hRoots]
    exact (mul_le_mul_of_nonneg_left (lpf_inverse_power_range_tail_le K L hK1)
      (by positivity : 0 <= 1 / Real.sqrt (d : Real))).trans hInv

end PrimeFactorOscillations.LPF
