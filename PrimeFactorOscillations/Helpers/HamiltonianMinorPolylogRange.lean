/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentReindex

/-! # One scalar threshold for every polylogarithmic minor

The threshold is uniform in the deleted supports and entry cap.
It simultaneously preserves order, the strong repair range and the
entry exponent required by the complete smaller permanent theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_repaired_logarithmic_cap (n m a K : Real)
    (hn : 4 <= n) (hm : n / 2 <= m) (hK : 0 <= K)
    (hLarge : Real.exp ((2 : Real) ^ (K + 1)) <= m)
    (hA : a <= (Real.log n) ^ K) :
    2 * a <= (Real.log m) ^ (K + 1) := by
  have hn0 : 0 < n := by linarith only [hn]
  have hm0 : 0 < m := by linarith only [hm, hn]
  have hLogN : 0 < Real.log n := Real.log_pos (by linarith only [hn])
  have hSquare : n <= m ^ 2 := by nlinarith only [hn, hm]
  have hLogSquare := Real.log_le_log hn0 hSquare
  rw [Real.log_pow] at hLogSquare
  norm_num only [Nat.cast_ofNat] at hLogSquare
  have hLogCompare : Real.log n <= 2 * Real.log m := by linarith only [hLogSquare]
  have hLogLarge : (2 : Real) ^ (K + 1) <= Real.log m := by
    have h := Real.log_le_log (Real.exp_pos _) hLarge
    simpa only [Real.log_exp] using h
  have hLogM0 : 0 <= Real.log m := le_trans (Real.rpow_nonneg (by norm_num) _) hLogLarge
  have hPower := Real.rpow_le_rpow (le_of_lt hLogN) hLogCompare hK
  rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hLogM0] at hPower
  have hTwoPower : 2 * (2 : Real) ^ K = (2 : Real) ^ (K + 1) := by
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    ring
  calc
    _ <= 2 * (Real.log n) ^ K := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ <= 2 * ((2 : Real) ^ K * (Real.log m) ^ K) :=
      mul_le_mul_of_nonneg_left hPower (by norm_num)
    _ = (2 : Real) ^ (K + 1) * (Real.log m) ^ K := by rw [<- hTwoPower]; ring
    _ <= Real.log m * (Real.log m) ^ K :=
      mul_le_mul_of_nonneg_right hLogLarge (Real.rpow_nonneg hLogM0 _)
    _ = (Real.log m) ^ (K + 1) := by
      have hLogM : 0 < Real.log m := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hLogLarge
      rw [Real.rpow_add hLogM, Real.rpow_one]
      ring

theorem hamiltonian_minor_polylog_uniform_range (delta K : Real) (M : Nat)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    exists N0 : Nat, 32 <= N0 /\
      forall n : Nat, N0 <= n -> forall (r : Nat) (a : Real),
        (r : Real) <= (Real.log (2 * (n : Real))) ^ 3 ->
        1 <= a -> a <= (Real.log (n : Real)) ^ K ->
        (r : Real) * (a / delta) ^ 3 / (n : Real) <= 1 / 10000 /\
        (n : Real) / 2 <= ((n - r : Nat) : Real) /\
        M <= n - r /\ 16 <= n - r /\
        2 * a <= (Real.log ((n - r : Nat) : Real)) ^ (K + 1) := by
  let c := delta ^ 3 / 80000
  have hc : 0 < c := div_pos (pow_pos hDelta 3) (by norm_num)
  let range := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := (1 : Real))
      (3 + K * 3) (by norm_num)).bound hc)
  let x1 := range.choose
  let x0 := 32 + 2 * Real.exp ((2 : Real) ^ (K + 1)) + max 0 x1
  let N0 := max 32 (max (2 * M) (Nat.ceil x0))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn r a hR ha hA
  have hCeil : Nat.ceil x0 <= n :=
    le_trans (le_trans (le_max_right (2 * M) (Nat.ceil x0)) (le_max_right 32 _)) hn
  have hx : x0 <= (n : Real) := le_trans (Nat.le_ceil x0) (by exact_mod_cast hCeil)
  have hN32 : (32 : Real) <= (n : Real) := by
    exact_mod_cast le_trans (le_max_left 32 (max (2 * M) (Nat.ceil x0))) hn
  have hN0 : 0 < (n : Real) := by linarith only [hN32]
  have hNne : Not ((n : Real) = 0) := ne_of_gt hN0
  have hDne : Not (delta = 0) := ne_of_gt hDelta
  have hMax0 : 0 <= max 0 x1 := le_max_left _ _
  have hMax1 : x1 <= max 0 x1 := le_max_right _ _
  have hExp : 0 < Real.exp ((2 : Real) ^ (K + 1)) := Real.exp_pos _
  have hx1 : x1 <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hMax1, hExp]
  have hNExp : 2 * Real.exp ((2 : Real) ^ (K + 1)) <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hMax0]
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hN32])
  have hLog0 : 0 <= Real.log (n : Real) := le_of_lt hLog
  have hLogTwo : Real.log 2 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) (by linarith only [hN32])
  have hLogMul : Real.log (2 * (n : Real)) = Real.log 2 + Real.log (n : Real) :=
    Real.log_mul (by norm_num) hNne
  have hTwoLog : Real.log (2 * (n : Real)) <= 2 * Real.log (n : Real) := by
    linarith only [hLogMul, hLogTwo]
  have hLogDouble0 : 0 <= Real.log (2 * (n : Real)) :=
    Real.log_nonneg (by linarith only [hN32])
  have hRLog : (r : Real) <= 8 * Real.log (n : Real) ^ 3 := by
    have h := wick_nonnegative_power_le _ _ hLogDouble0 hTwoLog 3
    calc
      _ <= Real.log (2 * (n : Real)) ^ 3 := hR
      _ <= (2 * Real.log (n : Real)) ^ 3 := h
      _ = _ := by ring
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hAPower : a ^ 3 <= (Real.log (n : Real)) ^ (K * 3) := by
    calc
      _ <= ((Real.log (n : Real)) ^ K) ^ 3 :=
        wick_nonnegative_power_le _ _ ha0 hA 3
      _ = ((Real.log (n : Real)) ^ K) ^ (3 : Real) := (Real.rpow_natCast _ 3).symm
      _ = _ := (Real.rpow_mul hLog0 K 3).symm
  have hCombined : (r : Real) * a ^ 3 <=
      8 * (Real.log (n : Real)) ^ (3 + K * 3) := by
    calc
      _ <= (8 * Real.log (n : Real) ^ 3) * (Real.log (n : Real)) ^ (K * 3) :=
        mul_le_mul hRLog hAPower (pow_nonneg ha0 3)
          (mul_nonneg (by norm_num) (pow_nonneg hLog0 3))
      _ = _ := by
        have hThree : (Real.log (n : Real)) ^ (3 : Real) = Real.log (n : Real) ^ 3 := by
          simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (n : Real)) 3
        rw [Real.rpow_add hLog, hThree]
        ring
  have hBound := range.choose_spec (n : Real) hx1
  simp only [Real.norm_eq_abs, Real.rpow_one] at hBound
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 _), abs_of_pos hN0] at hBound
  have hNumerator : (r : Real) * a ^ 3 <= delta ^ 3 * (n : Real) / 10000 := by
    have h := mul_le_mul_of_nonneg_left hBound (by norm_num : (0 : Real) <= 8)
    dsimp only [c] at h
    nlinarith only [hCombined, h]
  have hClear : ((r : Real) * (a / delta) ^ 3 / (n : Real)) *
      (delta ^ 3 * (n : Real)) = (r : Real) * a ^ 3 := by
    field_simp [hDne, hNne]
    <;> ring
  have hStrong : (r : Real) * (a / delta) ^ 3 / (n : Real) <= 1 / 10000 := by
    apply le_of_mul_le_mul_right _ (mul_pos (pow_pos hDelta 3) hN0)
    rw [hClear]
    nlinarith only [hNumerator]
  have hD3 : delta ^ 3 <= 1 := by
    simpa only [one_pow] using wick_nonnegative_power_le delta 1 (le_of_lt hDelta) hDelta1 3
  have hA3 : 1 <= a ^ 3 := by
    simpa only [one_pow] using wick_nonnegative_power_le 1 a (by norm_num) ha 3
  have hr0 : 0 <= (r : Real) := Nat.cast_nonneg _
  have hRSize : (r : Real) <= (n : Real) / 10000 := by
    have h1 := mul_le_mul_of_nonneg_left hA3 hr0
    have h2 := mul_le_mul_of_nonneg_right hD3 (le_of_lt hN0)
    nlinarith only [h1, h2, hNumerator]
  have hRN : (r : Real) <= (n : Real) := by linarith only [hRSize, hN0]
  have hrn : r <= n := by exact_mod_cast hRN
  have hRank : (n : Real) / 2 <= ((n - r : Nat) : Real) := by
    rw [Nat.cast_sub hrn]
    linarith only [hRSize, hN0]
  have hMNat : 2 * M <= n :=
    le_trans (le_trans (le_max_left (2 * M) (Nat.ceil x0)) (le_max_right 32 _)) hn
  have hMReal : 2 * (M : Real) <= (n : Real) := by exact_mod_cast hMNat
  have hM : M <= n - r := by
    have h : (M : Real) <= ((n - r : Nat) : Real) := by linarith only [hMReal, hRank]
    exact_mod_cast h
  have hRank16 : 16 <= n - r := by
    have h : (16 : Real) <= ((n - r : Nat) : Real) := by linarith only [hN32, hRank]
    exact_mod_cast h
  have hCap := hamiltonian_repaired_logarithmic_cap (n : Real) ((n - r : Nat) : Real) a K
    (by linarith only [hN32]) hRank hK
    (by linarith only [hNExp, hRank]) hA
  exact And.intro hStrong (And.intro hRank (And.intro hM (And.intro hRank16 hCap)))

end PrimeFactorOscillations
