/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BufferedGreedyPrimeClass

/-!
# RH as finiteness of one fixed buffered deletion class

The buffer is fixed independently of RH. Both implications retain the
literal sequential class. The forward implication uses the maintained RH
theta envelope; the converse uses only the unconditional cofinal zero
criterion and the complete prime-error bound supplied by termination.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def rootLogCubeBuffer (n : Nat) : Real :=
  Real.sqrt (n : Real) * (Real.log (n : Real)) ^ 3

theorem rootLogCubeBuffer_nonneg (n : Nat) : 0 <= rootLogCubeBuffer n := by
  by_cases hn : n = 0
  case pos => simp [rootLogCubeBuffer, hn]
  case neg =>
    have hLog : 0 <= Real.log (n : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
    exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hLog 3)

theorem rootLogCubeBuffer_monotone : Monotone rootLogCubeBuffer := by
  intro X Y hXY
  by_cases hX : X = 0
  case pos =>
    simpa [rootLogCubeBuffer, hX] using rootLogCubeBuffer_nonneg Y
  case neg =>
    have hLogX : 0 <= Real.log (X : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= X by omega))
    have hLogXY : Real.log (X : Real) <= Real.log (Y : Real) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < X)) (Nat.cast_le.mpr hXY)
    have hLogY : 0 <= Real.log (Y : Real) := hLogX.trans hLogXY
    have hSquare := mul_le_mul hLogXY hLogXY hLogX hLogY
    have hCube : (Real.log (X : Real)) ^ 3 <= (Real.log (Y : Real)) ^ 3 := by
      have h := mul_le_mul hLogXY hSquare (mul_nonneg hLogX hLogX) hLogY
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
    exact mul_le_mul (Real.sqrt_le_sqrt (Nat.cast_le.mpr hXY)) hCube
      (pow_nonneg hLogX 3) (Real.sqrt_nonneg _)

theorem rootLogCubeBuffer_subpower_limit (epsilon : Real) (he : 0 < epsilon) :
    Tendsto (fun x : Real =>
      Real.sqrt x * (Real.log x) ^ 3 / x ^ ((1 / 2 : Real) + epsilon))
      atTop (nhds 0) := by
  let delta : Real := epsilon / 3
  have hd : 0 < delta := by dsimp only [delta]; linarith only [he]
  have hLog : Tendsto (fun x : Real => Real.log x / x ^ delta) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      gaussian_power_log_ratio_tendsto 0 delta hd
  have hCube : Tendsto (fun x : Real => (Real.log x / x ^ delta) ^ 3)
      atTop (nhds 0) := by simpa only [zero_pow (by omega : Not (3 = 0))] using hLog.pow 3
  apply hCube.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  have hExponent : (1 / 2 : Real) + epsilon =
      (1 / 2 : Real) + delta + delta + delta := by dsimp only [delta]; ring
  rw [Real.sqrt_eq_rpow, hExponent, Real.rpow_add hx, Real.rpow_add hx,
    Real.rpow_add hx]
  have hHalf : Not (x ^ (1 / 2 : Real) = 0) :=
    (Real.rpow_pos_of_pos hx (1 / 2 : Real)).ne'
  have hDelta : Not (x ^ delta = 0) := (Real.rpow_pos_of_pos hx delta).ne'
  field_simp [hHalf, hDelta] <;> ring

theorem rootLogCube_envelope_dominance (A C x : Real)
    (hA : 0 <= A) (hC : 0 <= C)
    (hLog : C + 2 <= Real.log x) (hRoot : A + 1 <= Real.sqrt x) :
    A + C * Real.sqrt x * (Real.log x) ^ 2 + Real.log x <=
      Real.sqrt x * (Real.log x) ^ 3 := by
  have hu : 2 <= Real.log x := by linarith only [hC, hLog]
  have hu0 : 0 <= Real.log x := by linarith only [hu]
  have hs : 0 <= Real.sqrt x := Real.sqrt_nonneg x
  have hSquare : Real.log x + 1 <= (Real.log x) ^ 2 := by nlinarith only [hu]
  have hScaled := mul_le_mul_of_nonneg_left hSquare hs
  have hSU : Real.log x <= Real.sqrt x * Real.log x := by
    have h := mul_nonneg (show 0 <= Real.sqrt x - 1 by linarith only [hRoot, hA]) hu0
    nlinarith only [h]
  have hRoom := mul_nonneg (mul_nonneg hs (sq_nonneg (Real.log x)))
    (show 0 <= Real.log x - C - 1 by linarith only [hLog])
  nlinarith only [hRoom, hScaled, hSU, hRoot]

theorem rootLogCubeBuffer_eventually_dominates_primeError_of_RH
    (hRH : RiemannHypothesis) :
    Exists fun N : Nat => forall n, N <= n ->
      primeClockError n <= rootLogCubeBuffer (primeAt n) := by
  choose A hA C hC hMass using greedyDeletedPrimeClass_RH_theta_mass_bound hRH
  let T := max (2 : Real) (max (Real.exp (C + 2)) ((A + 1) ^ 2))
  refine Exists.intro (Nat.ceil T) ?_
  intro n hn
  have hTp : T <= (primeAt n : Real) := (Nat.le_ceil T).trans
    (Nat.cast_le.mpr (hn.trans (primeAt_ge_index n)))
  have hExp : Real.exp (C + 2) <= (primeAt n : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hTp)
  have hLog : C + 2 <= Real.log (primeAt n : Real) := by
    have h := Real.log_le_log (Real.exp_pos (C + 2)) hExp
    simpa only [Real.log_exp] using h
  have hSquare : (A + 1) ^ 2 <= (primeAt n : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hTp)
  have hRoot : A + 1 <= Real.sqrt (primeAt n : Real) := by
    have h := Real.sqrt_le_sqrt hSquare
    simpa only [Real.sqrt_sq (show 0 <= A + 1 by linarith only [hA])] using h
  have hTheta := greedyPrimeClass_theta_partition (primeAt n)
  have hCap := greedyPrimeClass_theta_le (primeAt n)
  have hError : primeClockError n <= primeClassTheta greedyDeletedPrimeClass (primeAt n) := by
    rw [primeClockError_eq_theta]
    linarith only [hTheta, hCap]
  have hUpper := hMass (primeAt n) (prime_primeAt n).two_le
  have hBuffer := rootLogCube_envelope_dominance A C (primeAt n : Real) hA hC.le hLog hRoot
  exact hError.trans (hUpper.trans hBuffer)

theorem bufferedGreedyDeletedPrimeClass_finite_of_eventual_error_le_buffer
    (B : Nat -> Real)
    (hEventual : Exists fun N : Nat => forall n, N <= n ->
      primeClockError n <= B (primeAt n)) :
    Set.Finite (bufferedGreedyDeletedPrimeClass B) := by
  choose N hN using hEventual
  let C := clockRecord (bufferedPrimeClockError B) N
  have hC : 0 <= C := clockRecord_nonneg _ _
  apply (bufferedGreedyDeletedPrimeClass_finite_iff_bounded_excess B).mpr
  refine Exists.intro C (And.intro hC ?_)
  intro n
  by_cases hn : n < N
  case pos =>
    have hLocal := (clockRecord_contains (bufferedPrimeClockError B) n).trans
      (clockRecord_monotone (bufferedPrimeClockError B) (Nat.succ_le_of_lt hn))
    change primeClockError n - B (primeAt n) <= C at hLocal
    linarith only [hLocal]
  case neg =>
    have hLocal := hN n (le_of_not_gt hn)
    linarith only [hLocal, hC]

theorem rootLogCubeBuffered_deleted_finite_of_RH (hRH : RiemannHypothesis) :
    Set.Finite (bufferedGreedyDeletedPrimeClass rootLogCubeBuffer) :=
  bufferedGreedyDeletedPrimeClass_finite_of_eventual_error_le_buffer rootLogCubeBuffer
    (rootLogCubeBuffer_eventually_dominates_primeError_of_RH hRH)

theorem rootLogCubeBuffer_old_count_bound_of_bounded_excess
    (C : Real) (hC : 0 <= C)
    (he : forall n, primeClockError n <= rootLogCubeBuffer (primeAt n) + C)
    (X : Nat) (hX : 2 <= X) :
    ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * Real.log 2 <=
      rootLogCubeBuffer X + C + Real.log (X : Real) := by
  have hRecord : greedyPrimeRegulator X <= rootLogCubeBuffer X + C := by
    apply (greedyPrimeRegulator_le_iff X _).mpr
    refine And.intro (add_nonneg (rootLogCubeBuffer_nonneg X) hC) ?_
    intro p hp hpX
    have hLocal := he (Nat.count Nat.Prime p)
    rw [primeClockError_eq_theta, primeAt_count_prime p hp] at hLocal
    have hMono := rootLogCubeBuffer_monotone hpX
    linarith only [hLocal, hMono]
  have hMass := (greedyDeletedPrimeClass_record_bounds X hX).2
  have hCount := primeClassPrefix_count_mul_log_two_le_theta greedyDeletedPrimeClass X
  linarith only [hRecord, hMass, hCount]

theorem rootLogCubeBuffer_eventually_greedy_count_of_bounded_excess
    (C : Real) (hC : 0 <= C)
    (he : forall n, primeClockError n <= rootLogCubeBuffer (primeAt n) + C)
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun n : Nat =>
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
        (n : Real) ^ ((1 / 2 : Real) + epsilon)) atTop := by
  let a : Real := (1 / 2 : Real) + epsilon
  have ha : 0 < a := by dsimp only [a]; linarith only [hEpsilon]
  have hBuffer : Tendsto (fun x : Real => Real.sqrt x * (Real.log x) ^ 3 / x ^ a)
      atTop (nhds 0) := rootLogCubeBuffer_subpower_limit epsilon hEpsilon
  have hConstant : Tendsto (fun x : Real => C / x ^ a) atTop (nhds 0) :=
    (tendsto_rpow_atTop ha).const_div_atTop C
  have hLog : Tendsto (fun x : Real => Real.log x / x ^ a) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using gaussian_power_log_ratio_tendsto 0 a ha
  have hSum : Tendsto (fun x : Real =>
      Real.sqrt x * (Real.log x) ^ 3 / x ^ a + C / x ^ a + Real.log x / x ^ a)
      atTop (nhds 0) := by
    simpa only [zero_add, add_zero] using (hBuffer.add hConstant).add hLog
  have hTotal : Tendsto (fun x : Real =>
      (Real.sqrt x * (Real.log x) ^ 3 + C + Real.log x) / x ^ a)
      atTop (nhds 0) := by
    apply hSum.congr'
    exact Filter.Eventually.of_forall (fun x => by ring)
  have hNat : Tendsto (fun n : Nat =>
      (rootLogCubeBuffer n + C + Real.log (n : Real)) / (n : Real) ^ a)
      atTop (nhds 0) := hTotal.comp tendsto_natCast_atTop_atTop
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  filter_upwards [hNat.eventually (eventually_lt_nhds hLogTwo),
    eventually_ge_atTop (2 : Nat)] with n hSmall hn
  have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hPower : 0 < (n : Real) ^ a := Real.rpow_pos_of_pos hnPos a
  have hMul := mul_lt_mul_of_pos_right hSmall hPower
  have hCancel : ((rootLogCubeBuffer n + C + Real.log (n : Real)) /
      (n : Real) ^ a) * (n : Real) ^ a =
        rootLogCubeBuffer n + C + Real.log (n : Real) := by field_simp [hPower.ne']
  rw [hCancel] at hMul
  have hBound := rootLogCubeBuffer_old_count_bound_of_bounded_excess C hC he n hn
  by_contra hFail
  have hWrong := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hFail)) hLogTwo.le
  change (n : Real) ^ a * Real.log 2 <=
    ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 at hWrong
  linarith only [hWrong, hBound, hMul]

theorem riemannHypothesis_of_rootLogCubeBuffered_deleted_finite
    (hFinite : Set.Finite (bufferedGreedyDeletedPrimeClass rootLogCubeBuffer)) :
    RiemannHypothesis := by
  choose C hC he using
    (bufferedGreedyDeletedPrimeClass_finite_iff_bounded_excess rootLogCubeBuffer).mp hFinite
  apply riemannHypothesis_of_sparse_greedyDeletedPrimeClass_count
  intro epsilon hEpsilon N
  choose K hK using Filter.eventually_atTop.mp
    (rootLogCubeBuffer_eventually_greedy_count_of_bounded_excess C hC he epsilon hEpsilon)
  exact Exists.intro (max (max N 2) K)
    (And.intro (le_max_left _ _) (hK _ (le_max_right _ _)))

theorem riemannHypothesis_iff_rootLogCubeBuffered_deleted_finite :
    RiemannHypothesis <->
      Set.Finite (bufferedGreedyDeletedPrimeClass rootLogCubeBuffer) :=
  Iff.intro rootLogCubeBuffered_deleted_finite_of_RH
    riemannHypothesis_of_rootLogCubeBuffered_deleted_finite

theorem rootLogCubeBuffered_theta_le (X : Nat) :
    primeClassTheta (bufferedGreedyPrimeClass rootLogCubeBuffer) X <=
      (X : Real) + rootLogCubeBuffer X :=
  bufferedGreedyPrimeClass_theta_le rootLogCubeBuffer rootLogCubeBuffer_monotone
    rootLogCubeBuffer_nonneg X

end PrimeFactorOscillations.PrimeClassDeletion
