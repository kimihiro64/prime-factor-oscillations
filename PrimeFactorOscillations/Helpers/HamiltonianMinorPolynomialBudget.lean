/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorTwoPower

/-! # A common polynomial envelope for the minor remainders

Only the analytic smallness and Taylor remainders use this unsigned
envelope. It does not replace the signed first-order correction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianMinorPolynomialConstant (delta : Real) : Real :=
  20100 + 4 * (12200002 + 4 * abs (hamiltonianPermanentUniformBudget delta) +
    16 * (2 : Real) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2)))

theorem hamiltonian_minor_polynomial_budget
    (delta r a : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hr : 0 <= r) (ha : 1 <= a) :
    let W := (1 + r) ^ 4 * (1 + a / delta) ^ 24
    0 < hamiltonianMinorPolynomialConstant delta /\
    0 <= hamiltonianMinorLogBudget delta r a /\
    100 * (1 + r) ^ 2 * (a / delta) ^ 2 + hamiltonianMinorLogBudget delta r a <=
      hamiltonianMinorPolynomialConstant delta * W /\
    hamiltonianMinorTwoPowerBudget delta r a <=
      hamiltonianMinorPolynomialConstant delta * W := by
  let p := a / delta
  let H := 1 + r
  let P := 1 + p
  let W := H ^ 4 * P ^ 24
  let c := 12200002 + 4 * abs (hamiltonianPermanentUniformBudget delta) +
    16 * (2 : Real) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2))
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hap : a <= p := by nlinarith only [hpClear, hp0, hDelta1]
  have hH1 : 1 <= H := by dsimp only [H]; linarith only [hr]
  have hP1 : 1 <= P := by dsimp only [P]; linarith only [hp0]
  have hH0 : 0 <= H := le_trans (by norm_num) hH1
  have hP0 : 0 <= P := le_trans (by norm_num) hP1
  have hUnitPower (x : Real) (hx : 1 <= x) (j : Nat) : 1 <= x ^ j := by
    induction j with
    | zero => simp only [pow_zero, le_refl]
    | succ j ih =>
      simpa only [pow_succ, one_mul] using
        mul_le_mul ih hx (by norm_num : (0 : Real) <= 1) (le_trans (by norm_num) ih)
  have hPowerMono (x : Real) (hx : 1 <= x) (j k : Nat) (hjk : j <= k) : x ^ j <= x ^ k := by
    have h := mul_le_mul_of_nonneg_left (hUnitPower x hx (k - j))
      (pow_nonneg (le_trans (by norm_num) hx) j)
    simpa only [mul_one, <- pow_add, Nat.add_sub_of_le hjk] using h
  have hR (j : Nat) (hj : j <= 4) : r ^ j <= H ^ 4 := by
    calc
      _ <= H ^ j := wick_nonnegative_power_le _ _ hr (by dsimp only [H]; linarith) j
      _ <= _ := hPowerMono H hH1 j 4 hj
  have hP (j : Nat) (hj : j <= 24) : p ^ j <= P ^ 24 := by
    calc
      _ <= P ^ j := wick_nonnegative_power_le _ _ hp0 (by dsimp only [P]; linarith) j
      _ <= _ := hPowerMono P hP1 j 24 hj
  have hH (j : Nat) (hj : j <= 4) : H ^ j <= H ^ 4 := hPowerMono H hH1 j 4 hj
  have hPP (j : Nat) (hj : j <= 24) : P ^ j <= P ^ 24 := hPowerMono P hP1 j 24 hj
  have hW0 : 0 <= W := mul_nonneg (pow_nonneg hH0 4) (pow_nonneg hP0 24)
  have hMono (j k : Nat) (hj : j <= 4) (hk : k <= 24) : r ^ j * p ^ k <= W :=
    mul_le_mul (hR j hj) (hP k hk) (pow_nonneg hp0 k) (pow_nonneg hH0 4)
  have hRank : r * (r + 1) <= W := by
    have hRH : r * (r + 1) <= H ^ 2 := by
      have h := mul_le_mul_of_nonneg_right
        (show r <= H by dsimp only [H]; linarith) (show 0 <= r + 1 by linarith only [hr])
      dsimp only [H] at h
      nlinarith only [h]
    have hOneP : 1 <= P ^ 24 := by simpa only [pow_zero] using hPP 0 (by norm_num)
    calc
      _ <= H ^ 2 := hRH
      _ <= H ^ 4 := hH 2 (by norm_num)
      _ <= W := by
        have h := mul_le_mul_of_nonneg_left hOneP (pow_nonneg hH0 4)
        simpa only [mul_one] using h
  have hOneH : 1 <= H ^ 4 := by simpa only [pow_zero] using hH 0 (by norm_num)
  have hPV : P ^ 24 <= W := by
    have h := mul_le_mul_of_nonneg_right hOneH (pow_nonneg hP0 24)
    simpa only [one_mul] using h
  have hOld : (1 + a) ^ 24 <= W := by
    calc
      _ <= P ^ 24 := wick_nonnegative_power_le _ _ (by linarith only [ha])
        (by dsimp only [P]; linarith only [hap]) 24
      _ <= _ := hPV
  have hNew : (1 + 2 * a) ^ 24 <= (2 : Real) ^ 24 * W := by
    calc
      _ <= (2 * P) ^ 24 := wick_nonnegative_power_le _ _ (by linarith only [ha])
        (by dsimp only [P]; linarith only [hap]) 24
      _ = (2 : Real) ^ 24 * P ^ 24 := mul_pow _ _ _
      _ <= _ := mul_le_mul_of_nonneg_left hPV (by norm_num)
  have hLog : hamiltonianMinorLogBudget delta r a <= c * W := by
    have h1 := mul_le_mul_of_nonneg_left (hMono 3 3 (by norm_num) (by norm_num))
      (by norm_num : (0 : Real) <= 200000)
    have h2 := mul_le_mul_of_nonneg_left (hMono 2 6 (by norm_num) (by norm_num))
      (by norm_num : (0 : Real) <= 10000000)
    have h3 := mul_le_mul_of_nonneg_left (hMono 1 6 (by norm_num) (by norm_num))
      (by norm_num : (0 : Real) <= 2000000)
    have h4 := mul_le_mul_of_nonneg_left hRank (by norm_num : (0 : Real) <= 2)
    have h5 := mul_le_mul_of_nonneg_left hOld
      (mul_nonneg (by norm_num : (0 : Real) <= 4) (abs_nonneg (hamiltonianPermanentUniformBudget delta)))
    have h6 := mul_le_mul_of_nonneg_left hNew
      (mul_nonneg (by norm_num : (0 : Real) <= 16) (abs_nonneg (hamiltonianPermanentUniformBudget (delta / 2))))
    have hSum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6
    have hAlgebra (w x y : Real) :
        200000 * w + 10000000 * w + 2000000 * w + 2 * w +
          (4 * x) * w + (16 * y) * ((2 : Real) ^ 24 * w) =
            (12200002 + 4 * x + 16 * (2 : Real) ^ 24 * y) * w := by ring
    have hEq := hAlgebra W (abs (hamiltonianPermanentUniformBudget delta))
      (abs (hamiltonianPermanentUniformBudget (delta / 2)))
    apply le_trans ?_ (le_of_eq hEq)
    dsimp only [hamiltonianMinorLogBudget]
    simpa only [p, pow_one, mul_assoc] using hSum
  have hA : (1 + r) ^ 2 * p ^ 2 <= W :=
    mul_le_mul (hH 2 (by norm_num)) (hP 2 (by norm_num)) (sq_nonneg p) (pow_nonneg hH0 4)
  have hT : (1 + r) ^ 4 * p ^ 4 <= W :=
    mul_le_mul (le_refl _) (hP 4 (by norm_num)) (pow_nonneg hp0 4) (pow_nonneg hH0 4)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hConstant : hamiltonianMinorPolynomialConstant delta = 20100 + 4 * c := rfl
  have hBudget0 : 0 <= hamiltonianMinorLogBudget delta r a := by
    dsimp only [hamiltonianMinorLogBudget]
    positivity
  refine And.intro (by rw [hConstant]; linarith only [hc]) (And.intro hBudget0 ?_)
  constructor
  case left =>
    change 100 * (1 + r) ^ 2 * p ^ 2 + hamiltonianMinorLogBudget delta r a <= _
    rw [hConstant]
    calc
      _ <= 100 * W + c * W := by
        have h := add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : Real) <= 100)) hLog
        simpa only [mul_assoc] using h
      _ = (100 + c) * W := (add_mul 100 c W).symm
      _ <= _ := mul_le_mul_of_nonneg_right (by linarith only [hc]) hW0
  case right =>
    change 20000 * (1 + r) ^ 4 * p ^ 4 + 3 * hamiltonianMinorLogBudget delta r a <= _
    rw [hConstant]
    calc
      _ <= 20000 * W + 3 * (c * W) := by
        have h := add_le_add
          (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : Real) <= 20000))
          (mul_le_mul_of_nonneg_left hLog (by norm_num : (0 : Real) <= 3))
        simpa only [mul_assoc] using h
      _ = (20000 + 3 * c) * W := by
        have hAlgebra (x y : Real) : 20000 * y + 3 * (x * y) = (20000 + 3 * x) * y := by ring
        exact hAlgebra c W
      _ <= _ := mul_le_mul_of_nonneg_right (by linarith only [hc]) hW0

end PrimeFactorOscillations
