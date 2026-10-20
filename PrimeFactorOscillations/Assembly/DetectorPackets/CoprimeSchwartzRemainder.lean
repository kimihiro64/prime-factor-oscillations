/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzMiddle

/-!
# CoprimeSchwartzRemainder

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.CoprimeSchwartzRemainder

open CoprimeSchwartzMixed CoprimeSchwartzLow CoprimeSchwartzHigh CoprimeSchwartzMiddle

theorem nonneg_nat_power_mono (a b : Real) (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    a ^ n <= b ^ n := by
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow ha hab (show (0 : Real) <= (n : Real) by positivity)

theorem inverse_nat_power_mono (b : Real) (hb : 1 <= b)
    (i j : Nat) (hij : i <= j) : 1 / b ^ j <= 1 / b ^ i := by
  have hpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have he : (i : Real) <= (j : Real) := by exact_mod_cast hij
  have hp : b ^ i <= b ^ j := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hb he
  exact one_div_le_one_div_of_le (pow_pos hpos _) hp

theorem middleTail_normalized (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q L : Nat) (X Y Z B : Real), 0 < q -> 1 <= L -> 0 < X ->
      0 < B -> X * B <= Z -> (Z / X) ^ 2 <= (L : Real) ->
      norm (middleTail q X Y Z L f) <= C * X / B ^ (k - 2) := by
  choose C hC hc using middleTail_norm_bound f k hk
  refine Exists.intro C (And.intro hC ?_)
  intro q L X Y Z B hq hL hX hB hXB hFreq
  have hZ : 0 < Z := lt_of_lt_of_le (mul_pos hX hB) hXB
  let T : Real := Z / X
  have hT : 0 < T := div_pos hZ hX
  have hBT : B <= T := by
    apply le_of_mul_le_mul_left (a := X) ?_ hX
    calc
      _ <= Z := hXB
      _ = _ := by dsimp only [T]; field_simp
  have hZT : Z = X * T := by dsimp only [T]; field_simp
  have hkEq : k = (k - 1) + 1 := by omega
  have hXpow : X ^ k = X ^ (k - 1) * X := by
    calc
      _ = X ^ ((k - 1) + 1) := congrArg (fun j : Nat => X ^ j) hkEq
      _ = _ := pow_succ _ _
  have hExp : 2 * (k - 1) = k + (k - 2) := by omega
  have hTpow : (T ^ 2) ^ (k - 1) = T ^ k * T ^ (k - 2) := by
    rw [<- pow_mul, hExp, pow_add]
  have hLPow : (T ^ 2) ^ (k - 1) <= (L : Real) ^ (k - 1) :=
    nonneg_nat_power_mono _ _ (by positivity) hFreq _
  calc
    _ <= C * Z ^ k / (X ^ (k - 1) * (L : Real) ^ (k - 1)) :=
      hc q L X Y Z hq hL hX hZ
    _ = C * X * T ^ k / (L : Real) ^ (k - 1) := by
      rw [hZT, mul_pow, hXpow]
      field_simp <;> ring
    _ <= C * X * T ^ k / (T ^ 2) ^ (k - 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hLPow
    _ = C * X / T ^ (k - 2) := by
      rw [hTpow]
      field_simp [ne_of_gt hT]
    _ <= C * X / B ^ (k - 2) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hB _)
        (nonneg_nat_power_mono B T hB.le hBT _)

theorem remainder_max_bound (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q L : Nat) (X Y Z J : Real), 0 < q -> 1 <= L ->
      0 < X -> 0 < Y -> Y <= X -> X <= Z -> 0 < J ->
      Y * J <= X -> X * J <= Z -> (Z / X) ^ 2 <= (L : Real) ->
      norm (remainder q X Y Z L f) <= C * X / (max 1 J) ^ (k - 2) := by
  choose CLo hCLo hlo using lowDual_gain f k hk
  choose CHi hCHi hhi using highPrimal_norm_bound f k hk
  choose CMid hCMid hmid using middleTail_normalized f k hk
  refine Exists.intro (CLo + CMid + CHi) (And.intro (by positivity) ?_)
  intro q L X Y Z J hq hL hX hY hYX hXZ hJ hYJ hXJ hFreq
  let B : Real := max 1 J
  have hB1 : 1 <= B := le_max_left _ _
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  have hZ : 0 < Z := lt_of_lt_of_le hX hXZ
  have hYB : Y * B <= X := by
    dsimp only [B]
    by_cases h : 1 <= J
    next => rw [max_eq_right h]; exact hYJ
    next => rw [max_eq_left (lt_of_not_ge h).le, mul_one]; exact hYX
  have hXB : X * B <= Z := by
    dsimp only [B]
    by_cases h : 1 <= J
    next => rw [max_eq_right h]; exact hXJ
    next => rw [max_eq_left (lt_of_not_ge h).le, mul_one]; exact hXZ
  have hloB : norm (lowDual q X Y f) <= CLo * X / B ^ (k - 2) := by
    calc
      _ <= CLo * X / B ^ k := hlo q X Y B hq hX hY hB hYB
      _ = CLo * X * (1 / B ^ k) := by ring
      _ <= CLo * X * (1 / B ^ (k - 2)) :=
        mul_le_mul_of_nonneg_left
          (inverse_nat_power_mono B hB1 (k - 2) k (by omega)) (by positivity)
      _ = _ := by ring
  have hquot : X / Z <= 1 / B := by
    apply le_of_mul_le_mul_left (a := Z * B) ?_ (mul_pos hZ hB)
    calc
      _ = X * B := by field_simp
      _ <= Z := hXB
      _ = _ := by field_simp
  have hhiB : norm (highPrimal q X Z f) <= CHi * X / B ^ (k - 2) := by
    calc
      _ <= CHi * X * (X / Z) ^ (k - 1) := hhi q X Z hX hZ
      _ <= CHi * X * (1 / B) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left
          (nonneg_nat_power_mono _ _ (by positivity) hquot _) (by positivity)
      _ = CHi * X * (1 / B ^ (k - 1)) := by rw [div_pow, one_pow]
      _ <= CHi * X * (1 / B ^ (k - 2)) :=
        mul_le_mul_of_nonneg_left
          (inverse_nat_power_mono B hB1 (k - 2) (k - 1) (by omega)) (by positivity)
      _ = _ := by ring
  have hmidB : norm (middleTail q X Y Z L f) <= CMid * X / B ^ (k - 2) :=
    hmid q L X Y Z B hq hL hX hB hXB hFreq
  calc
    _ <= norm (lowDual q X Y f) + norm (middleTail q X Y Z L f) +
        norm (highPrimal q X Z f) := by
      dsimp only [remainder]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ <= CLo * X / B ^ (k - 2) + CMid * X / B ^ (k - 2) +
        CHi * X / B ^ (k - 2) := add_le_add (add_le_add hloB hmidB) hhiB
    _ = _ := by ring

theorem remainder_arbitrary_power (f : SchwartzMap Real Complex) (A : Real) (hA : 0 < A) :
    exists C : Real, 0 < C /\
      forall (q L : Nat) (X Y Z J : Real), 0 < q -> 1 <= L ->
      0 < X -> 0 < Y -> Y <= X -> X <= Z -> 0 < J ->
      Y * J <= X -> X * J <= Z -> (Z / X) ^ 2 <= (L : Real) ->
      norm (remainder q X Y Z L f) <= C * X / J ^ A := by
  choose C hC hc using remainder_max_bound f (Nat.ceil A + 2) (by omega)
  refine Exists.intro C (And.intro hC ?_)
  intro q L X Y Z J hq hL hX hY hYX hXZ hJ hYJ hXJ hFreq
  have hmain : norm (remainder q X Y Z L f) <=
      C * X / (max 1 J) ^ (Nat.ceil A) := by
    simpa only [Nat.add_sub_cancel] using
      hc q L X Y Z J hq hL hX hY hYX hXZ hJ hYJ hXJ hFreq
  have hp : J ^ A <= (max 1 J) ^ (Nat.ceil A) := by
    calc
      _ <= (max 1 J) ^ A := Real.rpow_le_rpow hJ.le (le_max_right _ _) hA.le
      _ <= (max 1 J) ^ ((Nat.ceil A : Nat) : Real) :=
        Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (Nat.le_ceil A)
      _ = _ := Real.rpow_natCast _ _
  exact hmain.trans
    (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hJ A) hp)

end PrimeFactorOscillations.CoprimeSchwartzRemainder

