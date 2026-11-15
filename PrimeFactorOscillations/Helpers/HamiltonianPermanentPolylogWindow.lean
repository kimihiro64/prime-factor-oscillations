/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Helpers.HamiltonianPermanentLocalExpansion

/-! # Uniform local correction for every fixed polylogarithmic entry cap

The finite quantitative size condition is discharged uniformly in A.
The resulting theorem concerns the actual stochastic observable at every
physical-window point, with one threshold for all kernels and caps.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_permanent_polylog_real_cutoff (delta K : Real)
    (hDelta0 : 0 < delta) :
    Exists (fun x0 : Real => forall x : Real, x0 <= x ->
      forall a : Real, 1 <= a -> a <= (Real.log x) ^ K ->
        hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt x) := by
  let c := 1001 * (192 * Real.exp 1) ^ 3 / delta ^ 5
  have hc : 0 < c := by dsimp [c]; positivity
  let eps := 1 / (64 * c)
  have hEps : 0 < eps := by dsimp [eps]; positivity
  have hLittle := _root_.isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : Real))
    (6 * K) (by norm_num)
  have hBound := hLittle.bound hEps
  let x0 := (Filter.eventually_atTop.mp hBound).choose
  have hx0 := (Filter.eventually_atTop.mp hBound).choose_spec
  refine Exists.intro (max 1 x0) ?_
  intro x hx a ha hA
  have hx1 : 1 <= x := le_trans (le_max_left 1 x0) hx
  have hxBase : x0 <= x := le_trans (le_max_right 1 x0) hx
  have hx0Nonneg : 0 <= x := le_trans (by norm_num) hx1
  have hLog0 : 0 <= Real.log x := Real.log_nonneg hx1
  have hRaw := hx0 x hxBase
  simp only [Real.norm_eq_abs] at hRaw
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 (6 * K)),
    abs_of_nonneg (Real.rpow_nonneg hx0Nonneg (1 / 2 : Real)),
    <- Real.sqrt_eq_rpow x] at hRaw
  have hFirst := wick_nonnegative_power_le (1 + a) (2 * a)
    (by linarith) (by linarith) 6
  have hSecond := wick_nonnegative_power_le a ((Real.log x) ^ K)
    (by linarith) hA 6
  have hPowerIdentity : ((Real.log x) ^ K) ^ 6 = (Real.log x) ^ (6 * K) := by
    calc
      _ = ((Real.log x) ^ K) ^ (6 : Real) := (Real.rpow_natCast _ 6).symm
      _ = (Real.log x) ^ (K * 6) := (Real.rpow_mul hLog0 K 6).symm
      _ = _ := congrArg (fun r : Real => (Real.log x) ^ r) (by ring)
  have hPower : (1 + a) ^ 6 <= 64 * (Real.log x) ^ (6 * K) := by
    calc
      _ <= (2 * a) ^ 6 := hFirst
      _ = 64 * a ^ 6 := by ring
      _ <= 64 * ((Real.log x) ^ K) ^ 6 :=
        mul_le_mul_of_nonneg_left hSecond (by norm_num)
      _ = _ := by rw [hPowerIdentity]
  calc
    _ = c * (1 + a) ^ 6 := by unfold hamiltonianPermanentCutoffThreshold; dsimp [c]; ring
    _ <= c * (64 * (Real.log x) ^ (6 * K)) :=
      mul_le_mul_of_nonneg_left hPower hc.le
    _ = (64 * c) * (Real.log x) ^ (6 * K) := by ring
    _ <= (64 * c) * (eps * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hRaw (by positivity)
    _ = _ := by dsimp only [eps]; field_simp [ne_of_gt hc]

theorem hamiltonian_permanent_polylog_nat_cutoff (delta K : Real)
    (hDelta0 : 0 < delta) :
    Exists (fun N0 : Nat => And (11 <= N0)
      (forall n : Nat, N0 <= n -> forall a : Real,
        1 <= a -> a <= (Real.log (n : Real)) ^ K ->
          hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real))) := by
  let hRange := hamiltonian_permanent_polylog_real_cutoff delta K hDelta0
  let x0 := hRange.choose
  have hx0 := hRange.choose_spec
  let N0 := max 11 (Nat.ceil x0)
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn a ha hA
  have hNat : Nat.ceil x0 <= n := le_trans (le_max_right _ _) hn
  have hReal : x0 <= (n : Real) :=
    le_trans (Nat.le_ceil x0) (by exact_mod_cast hNat)
  exact hx0 (n : Real) hReal a ha hA

theorem stochastic_compensated_polylog_window_covariance_remainder (delta K : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    Exists (fun N0 : Nat => forall (n : Nat)
      (T : Matrix (Fin n) (Fin n) Real) (q a s : Real),
      N0 <= n -> (n : Real) * q = 1 -> 1 <= a ->
      a <= (Real.log (n : Real)) ^ K ->
      (forall i, Finset.sum Finset.univ (fun j => T i j) = 1) ->
      (forall j, Finset.sum Finset.univ (fun i => T i j) = 1) ->
      (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
      norm (centeredKernel T q) <= 1 - delta ->
      abs s <= hamiltonianWindowScale delta ->
      norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
        (1 + (covarianceCorrection
          (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) : Complex))) <=
        hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2) := by
  let hRange := hamiltonian_permanent_polylog_nat_cutoff delta K hDelta0
  let N0 := hRange.choose
  have hN0 := hRange.choose_spec
  refine Exists.intro N0 ?_
  intro n T q a s hn hq ha hA hRow hCol hNonneg hUpper hNorm hs
  exact stochastic_compensated_window_covariance_remainder T q a delta s
    (le_trans hN0.1 hn) hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hs
      (hN0.2 n hn a ha hA)

end PrimeFactorOscillations
