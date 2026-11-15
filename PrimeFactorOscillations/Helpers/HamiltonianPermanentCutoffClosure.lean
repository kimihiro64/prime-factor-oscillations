/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCutoffExistence

/-! # Closed uniform bound for the actual full signed low Wick approximation

The explicit size hypothesis discharges every auxiliary cutoff, root,
length and Cauchy-tail condition in the physical-window consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPermanentWindowKappa (delta a : Real) : Real :=
  2 * hamiltonianWindowScale delta ^ 2 * a /
    (1 - hamiltonianWindowScale delta * (1 - delta / 2))

def hamiltonianPermanentCircleKappa (delta a : Real) : Real :=
  2 * (hamiltonianWindowScale delta * hamiltonianWindowScale delta) ^ 2 * a /
    (1 - hamiltonianWindowScale delta * hamiltonianWindowScale delta * (1 - delta / 2))

def hamiltonianPermanentWindowRemainderConstant (delta a : Real) : Real :=
  1 + 11616 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 11 +
    28 * (16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 12 *
      hamiltonianPermanentCutoffUpper delta a ^ 4 +
    10 * (1 + 16 * Real.exp 1 * hamiltonianPermanentCircleKappa delta a) ^ 3

theorem stochastic_compensated_fullLow_window_closed_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 11 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      stochasticLowWickValue T q s) <=
      hamiltonianPermanentWindowRemainderConstant delta a / (n : Real) ^ 2 := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  let R : NNReal := Subtype.mk b hb0
  let H := hamiltonianPermanentCutoff delta a (n : Real)
  let u := hamiltonianPermanentCutoffRoot delta a (n : Real)
  let V := hamiltonianPermanentCutoffUpper delta a ^ 2
  let kappa := hamiltonianPermanentWindowKappa delta a
  let kappaR := hamiltonianPermanentCircleKappa delta a
  let C := 2 * abs s * b / (1 - abs s * b * (1 - delta)) *
    Real.sqrt ((n : Real) * (a - 1)) + abs s ^ 2 * b ^ 2 * (a - 1) / 2
  have hx : 1 <= (n : Real) := by exact_mod_cast (show 1 <= n by omega)
  have hThetaBase : b * (1 - delta / 2) < 1 := by
    have hG := hamiltonian_window_coefficient_gap delta hDelta0
    change 7 * delta / 16 <= 1 - b * (1 - delta / 2) at hG
    linarith
  have hTheta : b * (R : Real) * (1 - delta / 2) < 1 := by
    have hG := hamiltonian_window_circle_gap delta hDelta0
    change 3 * delta / 8 <= 1 - b * b * (1 - delta / 2) at hG
    change b * b * (1 - delta / 2) < 1
    linarith
  have hKappa0 : 0 <= kappa := by
    dsimp only [kappa, hamiltonianPermanentWindowKappa]
    exact div_nonneg (by positivity) (sub_pos.mpr hThetaBase).le
  have hKappa : kappa <= 6 * a / delta :=
    hamiltonian_window_coefficient_kappa_bound delta a hDelta0 hDelta1 (by linarith)
  have hRoot := hamiltonian_permanent_cutoff_root_bounds
    delta a (n : Real) hDelta0 hDelta1 ha hx hSize
  have hSmall := hamiltonian_permanent_cutoff_root_small
    delta a (n : Real) kappa hDelta0 hDelta1 ha hx hKappa0 hKappa hSize
  have hLength := hamiltonian_permanent_cutoff_square_bound
    delta a (n : Real) hDelta0 hDelta1 ha hx
  have hH := hamiltonian_permanent_cutoff_at_least_eleven
    delta a (n : Real) hDelta0 hDelta1 ha hx
  have hMain := stochastic_compensated_fullLow_window_remainder
    T q a delta b s u V R H hn hH hq ha hRow hCol hNonneg hUpper
      hDelta0 hDelta1 hNorm hb.1.le hs hb.1 hTheta
      hRoot.1 hRoot.2.1 hSmall hRoot.2.2 hLength
  have hLarge := (hamiltonian_permanent_cutoff_bounds
    delta a (n : Real) hDelta0 hDelta1 ha hx).1
  have hC : C <= 4 * a * Real.sqrt (n : Real) / delta :=
    hamiltonian_window_exponent_bound delta s (n : Real) a hDelta0 hDelta1 hx ha hs
  have hTail := hamiltonian_window_cauchy_tail_small
    delta a (n : Real) C H hDelta0 hDelta1 ha hx hLarge hC
  have hPlain := hamiltonian_window_cauchy_tail_small
    delta a (n : Real) 0 H hDelta0 hDelta1 ha hx hLarge (by positivity)
  simp only [Real.exp_zero, one_mul] at hPlain
  have hKappaR0 : 0 <= kappaR := by
    dsimp only [kappaR, hamiltonianPermanentCircleKappa]
    exact div_nonneg (by positivity) (sub_pos.mpr hTheta).le
  have hLow := mul_le_mul_of_nonneg_left hPlain
    (show 0 <= 10 * (1 + 16 * Real.exp 1 * kappaR) ^ 3 by positivity)
  change norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      stochasticLowWickValue T q s) <= _ at hMain
  change Real.exp C * (Inv.inv b) ^ (H + 1) / (1 - Inv.inv b) <= _ at hTail
  have hLow' :
      10 * (1 + 16 * Real.exp 1 * kappaR) ^ 3 * (Inv.inv b) ^ (H + 1) /
          (1 - Inv.inv b) <=
        (10 * (1 + 16 * Real.exp 1 * kappaR) ^ 3) / (n : Real) ^ 2 := by
    simpa only [b, mul_div_assoc, mul_one_div] using hLow
  calc
    _ <= _ := hMain
    _ <= 1 / (n : Real) ^ 2 +
        (11616 * (1 + 16 * Real.exp 1 * kappa) ^ 11 +
          28 * (16 * Real.exp 1 * kappa) ^ 12 * V ^ 2) / (n : Real) ^ 2 +
        (10 * (1 + 16 * Real.exp 1 * kappaR) ^ 3) / (n : Real) ^ 2 :=
      add_le_add (add_le_add hTail (le_refl _)) hLow'
    _ = _ := by
      dsimp only [hamiltonianPermanentWindowRemainderConstant, V, kappa, kappaR]
      ring

def hamiltonianPermanentWindowPolynomialConstant (delta : Real) : Real :=
  1 + 11616 * (1 + 96 * Real.exp 1 / delta) ^ 11 +
    28 * (96 * Real.exp 1 / delta) ^ 12 * (1001 / delta ^ 2) ^ 4 +
    10 * (1 + 128 * Real.exp 1 / delta) ^ 3

theorem hamiltonian_polynomial_power_bound (c w x : Real) (p q : Nat)
    (hc : 0 <= c) (hw : 1 <= w) (hx0 : 0 <= x)
    (hx : x <= c * w) (hpq : p <= q) :
    x ^ p <= c ^ p * w ^ q := by
  have hw0 : 0 <= w := le_trans (by norm_num) hw
  have hPow := wick_nonnegative_power_le x (c * w) hx0 hx p
  have hTail : 1 <= w ^ (q - p) := by
    have h := wick_nonnegative_power_le (1 : Real) w (by norm_num) hw (q - p)
    simpa only [one_pow] using h
  have hW : w ^ p <= w ^ q := by
    calc
      _ = w ^ p * 1 := (mul_one _).symm
      _ <= w ^ p * w ^ (q - p) :=
        mul_le_mul_of_nonneg_left hTail (pow_nonneg hw0 p)
      _ = _ := by rw [<- pow_add, Nat.add_sub_of_le hpq]
  calc
    _ <= (c * w) ^ p := hPow
    _ = c ^ p * w ^ p := mul_pow _ _ _
    _ <= _ := mul_le_mul_of_nonneg_left hW (pow_nonneg hc p)

theorem hamiltonian_permanent_window_constant_polynomial (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a) :
    hamiltonianPermanentWindowRemainderConstant delta a <=
      hamiltonianPermanentWindowPolynomialConstant delta * (1 + a) ^ 24 := by
  let w := 1 + a
  let c := 96 * Real.exp 1 / delta
  let d := 128 * Real.exp 1 / delta
  let v := 1001 / delta ^ 2
  let k := hamiltonianPermanentWindowKappa delta a
  let kr := hamiltonianPermanentCircleKappa delta a
  have hw : 1 <= w := by dsimp [w]; linarith
  have hw0 : 0 <= w := le_trans (by norm_num) hw
  have hc : 0 <= c := by dsimp [c]; positivity
  have hd : 0 <= d := by dsimp [d]; positivity
  have hv : 0 <= v := by dsimp [v]; positivity
  have hk : k <= 6 * a / delta :=
    hamiltonian_window_coefficient_kappa_bound delta a hDelta0 hDelta1 (by linarith)
  have hkr : kr <= 8 * a / delta :=
    hamiltonian_window_circle_kappa_bound delta a hDelta0 hDelta1 (by linarith)
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hGapR : 0 < 1 - hamiltonianWindowScale delta *
      hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_circle_gap delta hDelta0
    linarith
  have hk0 : 0 <= k := by dsimp [k, hamiltonianPermanentWindowKappa]; positivity
  have hkr0 : 0 <= kr := by dsimp [kr, hamiltonianPermanentCircleKappa]; positivity
  have hScaled : 16 * Real.exp 1 * k <= c * w := by
    calc
      _ <= 16 * Real.exp 1 * (6 * a / delta) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = c * a := by dsimp [c]; ring
      _ <= c * w := mul_le_mul_of_nonneg_left (by dsimp [w]; linarith) hc
  have hScaledR : 16 * Real.exp 1 * kr <= d * w := by
    calc
      _ <= 16 * Real.exp 1 * (8 * a / delta) :=
        mul_le_mul_of_nonneg_left hkr (by positivity)
      _ = d * a := by dsimp [d]; ring
      _ <= d * w := mul_le_mul_of_nonneg_left (by dsimp [w]; linarith) hd
  have hBase : 1 + 16 * Real.exp 1 * k <= (1 + c) * w := by
    nlinarith only [hScaled, hw]
  have hBaseR : 1 + 16 * Real.exp 1 * kr <= (1 + d) * w := by
    nlinarith only [hScaledR, hw]
  have hModerate := hamiltonian_polynomial_power_bound
    (1 + c) w (1 + 16 * Real.exp 1 * k) 11 24 (by positivity) hw (by positivity) hBase (by omega)
  have hHigh := hamiltonian_polynomial_power_bound
    c w (16 * Real.exp 1 * k) 12 12 hc hw (by positivity) hScaled (by omega)
  have hLow := hamiltonian_polynomial_power_bound
    (1 + d) w (1 + 16 * Real.exp 1 * kr) 3 24 (by positivity) hw (by positivity) hBaseR (by omega)
  have hUnit : 1 <= w ^ 24 := by
    have h := wick_nonnegative_power_le (1 : Real) w (by norm_num) hw 24
    simpa only [one_pow] using h
  have hV : hamiltonianPermanentCutoffUpper delta a ^ 4 = v ^ 4 * w ^ 12 := by
    dsimp only [hamiltonianPermanentCutoffUpper, v, w]
    ring
  have hHighV :
      (16 * Real.exp 1 * k) ^ 12 * hamiltonianPermanentCutoffUpper delta a ^ 4 <=
        c ^ 12 * v ^ 4 * w ^ 24 := by
    rw [hV]
    calc
      _ <= (c ^ 12 * w ^ 12) * (v ^ 4 * w ^ 12) :=
        mul_le_mul_of_nonneg_right hHigh (by positivity)
      _ = _ := by ring
  have hM := mul_le_mul_of_nonneg_left hModerate (by norm_num : (0 : Real) <= 11616)
  have hH := mul_le_mul_of_nonneg_left hHighV (by norm_num : (0 : Real) <= 28)
  have hL := mul_le_mul_of_nonneg_left hLow (by norm_num : (0 : Real) <= 10)
  change 1 + 11616 * (1 + 16 * Real.exp 1 * k) ^ 11 +
      28 * (16 * Real.exp 1 * k) ^ 12 * hamiltonianPermanentCutoffUpper delta a ^ 4 +
      10 * (1 + 16 * Real.exp 1 * kr) ^ 3 <= _
  change _ <= (1 + 11616 * (1 + c) ^ 11 + 28 * c ^ 12 * v ^ 4 +
    10 * (1 + d) ^ 3) * w ^ 24
  nlinarith only [hUnit, hM, hH, hL]

theorem stochastic_compensated_fullLow_window_polynomial_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 11 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      stochasticLowWickValue T q s) <=
      hamiltonianPermanentWindowPolynomialConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2 := by
  exact le_trans (stochastic_compensated_fullLow_window_closed_remainder
    T q a delta s hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hs hSize)
    (div_le_div_of_nonneg_right
      (hamiltonian_permanent_window_constant_polynomial delta a hDelta0 hDelta1 ha)
        (sq_nonneg _))

end PrimeFactorOscillations
