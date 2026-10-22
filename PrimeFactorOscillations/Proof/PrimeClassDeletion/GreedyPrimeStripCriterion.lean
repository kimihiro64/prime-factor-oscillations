/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasStripDegreeLocalization
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeCountLiminf

/-!
# General upper zero strip and cofinal greedy deletion-count equivalence

The fractional coefficient moment, full weighted formula and localization
supply the forward implication. The actual native regulator retains the
entire initial prime range and overshoot. The uniform bad-zero response
supplies the reverse at exactly the same cofinal integer cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_strip_count_mass_bound
    (eta delta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hd : 0 < delta) (hdOne : delta <= 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    Exists fun A : Real => And (0 <= A) (Exists fun C : Real => And (0 < C)
      (forall X : Nat, 2 <= X ->
        ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * Real.log 2 <=
          A + C * (X : Real) ^ (eta + delta / 2) + Real.log (X : Real))) := by
  choose C hC hPsi using exists_nicolasPsiError_le_strip_rpow
    eta delta hEtaHalf hEtaOne hd hdOne hUpper
  let T : Real := max 4 (2 * Real.exp 1)
  let A : Real := Chebyshev.theta T
  have hA : 0 <= A := Chebyshev.theta_nonneg T
  have hExponent : 0 <= eta + delta / 2 := by linarith only [hEtaHalf, hd]
  have hRecord (X : Nat) :
      greedyPrimeRegulator X <= A + C * (X : Real) ^ (eta + delta / 2) := by
    apply (greedyPrimeRegulator_le_iff X _).mpr
    apply And.intro (by positivity)
    intro p hp hpX
    rw [primeClassTheta_univ_eq_chebyshev]
    have hpNonneg : (0 : Real) <= (p : Real) := Nat.cast_nonneg p
    have hpXReal : (p : Real) <= (X : Real) := Nat.cast_le.mpr hpX
    by_cases hSmall : (p : Real) < T
    case pos =>
      have hMono := Chebyshev.theta_mono hSmall.le
      have hRest : 0 <= C * (X : Real) ^ (eta + delta / 2) := by positivity
      change Chebyshev.theta (p : Real) - (p : Real) <=
        Chebyshev.theta T + C * (X : Real) ^ (eta + delta / 2)
      linarith only [hMono, hpNonneg, hRest]
    case neg =>
      have hT : T <= (p : Real) := le_of_not_gt hSmall
      have hFour : (4 : Real) <= (p : Real) :=
        (le_max_left 4 (2 * Real.exp 1)).trans hT
      have hExp : 2 * Real.exp 1 <= (p : Real) :=
        (le_max_right 4 (2 * Real.exp 1)).trans hT
      have hLog : 1 <= Real.log ((p : Real) / 2) := by
        have h := Real.log_le_log (Real.exp_pos 1)
          (show Real.exp 1 <= (p : Real) / 2 by linarith only [hExp])
        simpa only [Real.log_exp] using h
      have hThetaPsi : Chebyshev.theta (p : Real) <= Chebyshev.psi (p : Real) :=
        Chebyshev.theta_le_psi (p : Real)
      have hErr := (le_abs_self _).trans (hPsi (p : Real) hFour hLog)
      have hPower := Real.rpow_le_rpow hpNonneg hpXReal hExponent
      have hScaled := mul_le_mul_of_nonneg_left hPower hC.le
      linarith only [hThetaPsi, hErr, hScaled, hA]
  apply Exists.intro A
  apply And.intro hA
  apply Exists.intro C
  apply And.intro hC
  intro X hX
  have hMass := (greedyDeletedPrimeClass_record_bounds X hX).2
  have hCount := primeClassPrefix_count_mul_log_two_le_theta greedyDeletedPrimeClass X
  have hReg := hRecord X
  linarith only [hCount, hMass, hReg]

theorem greedyDeletedPrimeClass_eventually_power_count_of_zero_strip
    (eta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta)
    (epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun n : Nat =>
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
        (n : Real) ^ (eta + epsilon)) atTop := by
  let delta : Real := min epsilon 1
  have hd : 0 < delta := lt_min he (by norm_num)
  have hdOne : delta <= 1 := min_le_right epsilon 1
  have hdE : delta <= epsilon := min_le_left epsilon 1
  choose A hA C hC hCount using greedyDeletedPrimeClass_strip_count_mass_bound
    eta delta hEtaHalf hEtaOne hd hdOne hUpper
  let a : Real := eta + delta / 2
  let b : Real := eta + epsilon
  have hb : 0 < b := by dsimp only [b]; linarith only [hEtaHalf, he]
  have hGap : a < b := by dsimp only [a, b]; linarith only [hdE, he]
  have hConstant : Tendsto (fun X : Real => A / X ^ b) atTop (nhds 0) :=
    (tendsto_rpow_atTop hb).const_div_atTop A
  have hMain : Tendsto (fun X : Real => C * (X ^ a / X ^ b)) atTop (nhds 0) := by
    simpa only [mul_zero] using (gaussian_power_ratio_tendsto a b hGap).const_mul C
  have hLast : Tendsto (fun X : Real => Real.log X / X ^ b) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using gaussian_power_log_ratio_tendsto 0 b hb
  have hSum : Tendsto (fun X : Real =>
      A / X ^ b + C * (X ^ a / X ^ b) + Real.log X / X ^ b) atTop (nhds 0) := by
    simpa only [zero_add, add_zero] using (hConstant.add hMain).add hLast
  have hTotal : Tendsto (fun X : Real =>
      (A + C * X ^ a + Real.log X) / X ^ b) atTop (nhds 0) := by
    apply hSum.congr'
    exact Filter.Eventually.of_forall (fun X => by ring)
  have hNat : Tendsto (fun n : Nat =>
      (A + C * (n : Real) ^ a + Real.log (n : Real)) / (n : Real) ^ b)
      atTop (nhds 0) := hTotal.comp tendsto_natCast_atTop_atTop
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  filter_upwards [hNat.eventually (eventually_lt_nhds hLogTwo),
    eventually_ge_atTop (2 : Nat)] with n hSmall hn
  have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hPower : 0 < (n : Real) ^ b := Real.rpow_pos_of_pos hnPos b
  have hMul := mul_lt_mul_of_pos_right hSmall hPower
  have hCancel : ((A + C * (n : Real) ^ a + Real.log (n : Real)) /
      (n : Real) ^ b) * (n : Real) ^ b =
        A + C * (n : Real) ^ a + Real.log (n : Real) := by field_simp [hPower.ne']
  rw [hCancel] at hMul
  have hBound := hCount n hn
  by_contra hFail
  have hWrong := mul_le_mul_of_nonneg_right
    (le_of_lt (lt_of_not_ge hFail)) hLogTwo.le
  change (n : Real) ^ b * Real.log 2 <=
    ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 at hWrong
  change ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 <=
    A + C * (n : Real) ^ a + Real.log (n : Real) at hBound
  linarith only [hWrong, hBound, hMul]

theorem greedyDeletedPrimeClass_zero_strip_iff_cofinal_count
    (eta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1) :
    (forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= eta) <->
      (forall epsilon : Real, 0 < epsilon -> forall N : Nat,
        Exists fun n : Nat => And (max N 2 <= n)
          (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
            (n : Real) ^ (eta + epsilon))) := by
  constructor
  case mp =>
    intro hStrip epsilon he N
    have hUpper (p : RiemannXiDivisorZeroIndex) :
        (riemannXiDivisorZeroValue p).re <= eta := by
      have hNative := (riemannXi_zero_iff_nontrivial_zeta_zero
        (riemannXiDivisorZeroValue p)).mp (riemannXiDivisorZeroValue_eq_zero p)
      exact hStrip _ hNative.1 hNative.2
    choose M hM using Filter.eventually_atTop.mp
      (greedyDeletedPrimeClass_eventually_power_count_of_zero_strip
        eta hEtaHalf hEtaOne hUpper epsilon he)
    exact Exists.intro (max (max N 2) M)
      (And.intro (le_max_left _ _) (hM _ (le_max_right _ _)))
  case mpr =>
    exact greedyDeletedPrimeClass_zero_strip_of_sparse_power_count eta hEtaHalf

theorem greedyDeletedPrimeClass_zero_strip_iff_log_count_liminf
    (eta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1) :
    (forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= eta) <->
        Filter.liminf (primeClassLogCount greedyDeletedPrimeClass) atTop <= eta := by
  rw [greedyDeletedPrimeClass_zero_strip_iff_cofinal_count eta hEtaHalf hEtaOne]
  exact (greedyDeletedPrimeClass_liminf_le_iff_sparse_power_count eta
    (by linarith only [hEtaHalf])).symm

end PrimeFactorOscillations.PrimeClassDeletion
