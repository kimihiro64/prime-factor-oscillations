/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolylogRange
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolynomialBudget

/-! # A single uniform threshold for the full minor error -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianMinorUniformConstant (delta : Real) : Real :=
  16 * hamiltonianMinorPolynomialConstant delta * (1 + 1 / delta) ^ 24

def hamiltonianMinorUniformExponent (K : Real) : Nat :=
  12 + 24 * Nat.ceil K

theorem hamiltonian_minor_uniform_error_range
    (delta K : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    0 < hamiltonianMinorUniformConstant delta /\
    exists N0 : Nat, 32 <= N0 /\
      forall n : Nat, N0 <= n -> forall (r : Nat) (a : Real),
        (r : Real) <= (Real.log (2 * (n : Real))) ^ 3 ->
        1 <= a -> a <= (Real.log (n : Real)) ^ K ->
        100 * (1 + (r : Real)) ^ 2 * (a / delta) ^ 2 / (n : Real) +
            hamiltonianMinorLogBudget delta (r : Real) a / (n : Real) ^ 2 <= 1 /\
        hamiltonianMinorTwoPowerBudget delta (r : Real) a / (n : Real) ^ 2 <=
          hamiltonianMinorUniformConstant delta *
            (Real.log (2 * (n : Real))) ^ hamiltonianMinorUniformExponent K / (n : Real) ^ 2 := by
  let C := hamiltonianMinorUniformConstant delta
  let M := hamiltonianMinorUniformExponent K
  let k := Nat.ceil K
  let d := 1 + 1 / delta
  have hPolyC : 0 < hamiltonianMinorPolynomialConstant delta :=
    (hamiltonian_minor_polynomial_budget delta 0 1 hDelta hDelta1 (by norm_num) (by norm_num)).1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hC : 0 < C := mul_pos (mul_pos (by norm_num) hPolyC) (pow_pos hd 24)
  have hTwo : 0 < (2 : Real) ^ M := pow_pos (by norm_num) M
  let c := 1 / (C * (2 : Real) ^ M)
  have hc : 0 < c := div_pos (by norm_num) (mul_pos hC hTwo)
  let range := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := (1 : Real)) (M : Real) (by norm_num)).bound hc)
  let x1 := range.choose
  let x0 := 32 + Real.exp 1 + max 0 x1
  let N0 := max 32 (Nat.ceil x0)
  refine And.intro hC (Exists.intro N0 (And.intro (le_max_left _ _) ?_))
  intro n hn r a hR ha hA
  have hCeil : Nat.ceil x0 <= n := le_trans (le_max_right 32 _) hn
  have hx : x0 <= (n : Real) := le_trans (Nat.le_ceil x0) (by exact_mod_cast hCeil)
  have hN32 : (32 : Real) <= (n : Real) := by
    exact_mod_cast le_trans (le_max_left 32 (Nat.ceil x0)) hn
  have hN0 : 0 < (n : Real) := by linarith only [hN32]
  have hN1 : 1 <= (n : Real) := by linarith only [hN32]
  have hNne : Not ((n : Real) = 0) := ne_of_gt hN0
  have hMax0 : 0 <= max 0 x1 := le_max_left _ _
  have hMax1 : x1 <= max 0 x1 := le_max_right _ _
  have hExp : 0 < Real.exp 1 := Real.exp_pos 1
  have hx1 : x1 <= (n : Real) := by dsimp only [x0] at hx; linarith only [hx, hMax1, hExp]
  have hExpN : Real.exp 1 <= (n : Real) := by dsimp only [x0] at hx; linarith only [hx, hMax0]
  have hLog1 : 1 <= Real.log (n : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExpN
    simpa only [Real.log_exp] using h
  have hLog0 : 0 <= Real.log (n : Real) := le_trans (by norm_num) hLog1
  have hLogPos : 0 < Real.log (n : Real) := lt_of_lt_of_le (by norm_num) hLog1
  let b := Real.log (2 * (n : Real))
  have hLogB : Real.log (n : Real) <= b :=
    Real.log_le_log hN0 (by nlinarith only [hN0])
  have hb1 : 1 <= b := le_trans hLog1 hLogB
  have hb0 : 0 <= b := le_trans (by norm_num) hb1
  have hLogTwo : Real.log 2 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) (by linarith only [hN32])
  have hBUpper : b <= 2 * Real.log (n : Real) := by
    have hMul := Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hNne
    change b = Real.log 2 + Real.log (n : Real) at hMul
    linarith only [hMul, hLogTwo]
  have hKCeil : K <= (k : Real) := Nat.le_ceil K
  have hACeil : a <= Real.log (n : Real) ^ k := by
    calc
      _ <= Real.log (n : Real) ^ K := hA
      _ <= Real.log (n : Real) ^ (k : Real) := by
        rw [Real.rpow_def_of_pos hLogPos, Real.rpow_def_of_pos hLogPos]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hKCeil (Real.log_nonneg hLog1))
      _ = _ := Real.rpow_natCast _ k
  have hAB : a <= b ^ k :=
    le_trans hACeil (wick_nonnegative_power_le _ _ hLog0 hLogB k)
  have hOneBK : 1 <= b ^ k := by
    simpa only [one_pow] using wick_nonnegative_power_le (1 : Real) b (by norm_num) hb1 k
  have hOneB3 : 1 <= b ^ 3 := by
    simpa only [one_pow] using wick_nonnegative_power_le (1 : Real) b (by norm_num) hb1 3
  have hH : 1 + (r : Real) <= 2 * b ^ 3 := by linarith only [hR, hOneB3]
  have hP : 1 + a / delta <= d * b ^ k := by
    calc
      _ <= b ^ k + b ^ k / delta :=
        add_le_add hOneBK (div_le_div_of_nonneg_right hAB (le_of_lt hDelta))
      _ = _ := by dsimp only [d]; ring
  have hW : (1 + (r : Real)) ^ 4 * (1 + a / delta) ^ 24 <=
      16 * d ^ 24 * b ^ M := by
    calc
      _ <= (2 * b ^ 3) ^ 4 * (d * b ^ k) ^ 24 :=
        mul_le_mul
          (wick_nonnegative_power_le _ _ (by positivity) hH 4)
          (wick_nonnegative_power_le _ _ (by positivity) hP 24)
          (pow_nonneg (by positivity) 24) (pow_nonneg (by positivity) 4)
      _ = 16 * d ^ 24 * ((b ^ 3) ^ 4 * (b ^ k) ^ 24) := by rw [mul_pow, mul_pow]; ring
      _ = _ := by
        rw [<- pow_mul, <- pow_mul, <- pow_add]
        simp only [M, hamiltonianMinorUniformExponent, k, Nat.reduceMul, Nat.mul_comm]
  have hPolynomial := hamiltonian_minor_polynomial_budget delta (r : Real) a hDelta hDelta1
    (Nat.cast_nonneg _) ha
  have hSmallNumerator : 100 * (1 + (r : Real)) ^ 2 * (a / delta) ^ 2 +
      hamiltonianMinorLogBudget delta (r : Real) a <= C * b ^ M := by
    calc
      _ <= _ := hPolynomial.2.2.1
      _ <= hamiltonianMinorPolynomialConstant delta * (16 * d ^ 24 * b ^ M) :=
        mul_le_mul_of_nonneg_left hW (le_of_lt hPolyC)
      _ = _ := by dsimp only [C, hamiltonianMinorUniformConstant, d]; ring
  have hErrorNumerator : hamiltonianMinorTwoPowerBudget delta (r : Real) a <= C * b ^ M := by
    calc
      _ <= _ := hPolynomial.2.2.2
      _ <= hamiltonianMinorPolynomialConstant delta * (16 * d ^ 24 * b ^ M) :=
        mul_le_mul_of_nonneg_left hW (le_of_lt hPolyC)
      _ = _ := by dsimp only [C, hamiltonianMinorUniformConstant, d]; ring
  have hBound := range.choose_spec (n : Real) hx1
  have hMPower : Real.log (n : Real) ^ (M : Real) = Real.log (n : Real) ^ M :=
    Real.rpow_natCast _ M
  simp only [Real.norm_eq_abs, Real.rpow_one, hMPower] at hBound
  rw [abs_of_nonneg (pow_nonneg hLog0 M), abs_of_pos hN0] at hBound
  have hBC := wick_nonnegative_power_le b (2 * Real.log (n : Real)) hb0 hBUpper M
  have hClear : (C * (2 : Real) ^ M) * c = 1 := by
    dsimp only [c]
    field_simp [ne_of_gt hC, ne_of_gt hTwo]
  have hCN : C * b ^ M <= (n : Real) := by
    calc
      _ <= C * ((2 * Real.log (n : Real)) ^ M) := mul_le_mul_of_nonneg_left hBC (le_of_lt hC)
      _ = (C * (2 : Real) ^ M) * Real.log (n : Real) ^ M := by rw [mul_pow]; ring
      _ <= (C * (2 : Real) ^ M) * (c * (n : Real)) :=
        mul_le_mul_of_nonneg_left hBound (le_of_lt (mul_pos hC hTwo))
      _ = _ := by rw [<- mul_assoc, hClear, one_mul]
  have hInv : 1 / (n : Real) ^ 2 <= 1 / (n : Real) := by
    have hLeft : (1 / (n : Real) ^ 2) * (n : Real) ^ 2 = 1 := by field_simp [hNne]
    have hRight : (1 / (n : Real)) * (n : Real) ^ 2 = (n : Real) := by field_simp [hNne]
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos hN0)
    rw [hLeft, hRight]
    exact hN1
  have hBReduce : hamiltonianMinorLogBudget delta (r : Real) a / (n : Real) ^ 2 <=
      hamiltonianMinorLogBudget delta (r : Real) a / (n : Real) := by
    calc
      _ = hamiltonianMinorLogBudget delta (r : Real) a * (1 / (n : Real) ^ 2) := by ring
      _ <= hamiltonianMinorLogBudget delta (r : Real) a * (1 / (n : Real)) :=
        mul_le_mul_of_nonneg_left hInv hPolynomial.2.1
      _ = _ := by ring
  refine And.intro ?_ (div_le_div_of_nonneg_right hErrorNumerator (sq_nonneg (n : Real)))
  calc
    _ <= (100 * (1 + (r : Real)) ^ 2 * (a / delta) ^ 2 +
        hamiltonianMinorLogBudget delta (r : Real) a) / (n : Real) := by
      rw [add_div]
      exact add_le_add (le_refl _) hBReduce
    _ <= (C * b ^ M) / (n : Real) := div_le_div_of_nonneg_right hSmallNumerator (le_of_lt hN0)
    _ <= 1 := (div_le_one hN0).2 hCN

end PrimeFactorOscillations
