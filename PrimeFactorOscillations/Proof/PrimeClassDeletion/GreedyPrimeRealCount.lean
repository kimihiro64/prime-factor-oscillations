/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHCount
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeStripCriterion

/-!
# Literal real-cutoff size criteria for the greedy deleted-prime class

All counts use the actual primes up to the floor of the real cutoff.
The reverse implication absorbs a fixed BigO constant using an explicit
exponent gap before applying the unconditional all-cutoff zero response.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassPrefix_real_power_bigO_of_eventually_nat
    (P : Set Nat) (a : Real) (ha : 0 <= a)
    (hCount : Filter.Eventually (fun n : Nat =>
      ((primeClassPrefix P n).card : Real) <= (n : Real) ^ a) atTop) :
    Asymptotics.IsBigO atTop
      (fun X : Real => ((primeClassPrefix P (Nat.floor X)).card : Real))
      (fun X : Real => X ^ a) := by
  choose N hN using Filter.eventually_atTop.mp hCount
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop ((max N 2 : Nat) : Real)] with X hX
  have hFloor : max N 2 <= Nat.floor X := Nat.le_floor hX
  have hX0 : (0 : Real) <= X := by
    have hTwo : (2 : Real) <= ((max N 2 : Nat) : Real) := by
      exact_mod_cast (le_max_right N 2)
    linarith only [hX, hTwo]
  have h := (hN _ ((le_max_left N 2).trans hFloor)).trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX0) ha)
  have hCard : (0 : Real) <= ((primeClassPrefix P (Nat.floor X)).card : Real) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hCard,
    abs_of_nonneg (Real.rpow_nonneg hX0 a), one_mul] using h

theorem primeClassPrefix_eventually_nat_power_of_real_power_bigO
    (P : Set Nat) (a b : Real) (hab : a < b)
    (hCount : Asymptotics.IsBigO atTop
      (fun X : Real => ((primeClassPrefix P (Nat.floor X)).card : Real))
      (fun X : Real => X ^ a)) :
    Filter.Eventually (fun n : Nat =>
      ((primeClassPrefix P n).card : Real) <= (n : Real) ^ b) atTop := by
  choose C hC using Asymptotics.isBigO_iff'.mp hCount
  have hNatBound := tendsto_natCast_atTop_atTop.eventually hC.2
  have hRatio : Tendsto (fun n : Nat =>
      C * ((n : Real) ^ a / (n : Real) ^ b)) atTop (nhds 0) := by
    have h := ((gaussian_power_ratio_tendsto a b hab).const_mul C).comp
      tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using h
  filter_upwards [hNatBound, hRatio.eventually (eventually_lt_nhds (by norm_num : (0 : Real) < 1)),
    eventually_ge_atTop (2 : Nat)] with n hBound hSmall hn
  have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hPower : 0 < (n : Real) ^ b := Real.rpow_pos_of_pos hnPos b
  have hCard : (0 : Real) <= ((primeClassPrefix P n).card : Real) := Nat.cast_nonneg _
  simp only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_nonneg hCard,
    abs_of_nonneg (Real.rpow_nonneg hnPos.le a)] at hBound
  have hMul := mul_lt_mul_of_pos_right hSmall hPower
  have hCancel : (C * ((n : Real) ^ a / (n : Real) ^ b)) * (n : Real) ^ b =
      C * (n : Real) ^ a := by field_simp [hPower.ne']
  rw [hCancel, one_mul] at hMul
  exact hBound.trans hMul.le

theorem greedyDeletedPrimeClass_zero_strip_iff_real_count_bigO
    (eta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1) :
    (forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= eta) <->
        (forall epsilon : Real, 0 < epsilon ->
          Asymptotics.IsBigO atTop
            (fun X : Real =>
              ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor X)).card : Real))
            (fun X : Real => X ^ (eta + epsilon))) := by
  constructor
  case mp =>
    intro hStrip epsilon he
    have hUpper (p : RiemannXiDivisorZeroIndex) :
        (riemannXiDivisorZeroValue p).re <= eta := by
      have hNative := (riemannXi_zero_iff_nontrivial_zeta_zero
        (riemannXiDivisorZeroValue p)).mp (riemannXiDivisorZeroValue_eq_zero p)
      exact hStrip _ hNative.1 hNative.2
    exact primeClassPrefix_real_power_bigO_of_eventually_nat greedyDeletedPrimeClass
      (eta + epsilon) (by linarith only [hEtaHalf, he])
      (greedyDeletedPrimeClass_eventually_power_count_of_zero_strip
        eta hEtaHalf hEtaOne hUpper epsilon he)
  case mpr =>
    intro hCount
    apply (greedyDeletedPrimeClass_zero_strip_iff_cofinal_count eta hEtaHalf hEtaOne).mpr
    intro epsilon he N
    have hEvent := primeClassPrefix_eventually_nat_power_of_real_power_bigO
      greedyDeletedPrimeClass (eta + epsilon / 2) (eta + epsilon)
      (by linarith only [he]) (hCount (epsilon / 2) (by linarith only [he]))
    choose M hM using Filter.eventually_atTop.mp hEvent
    exact Exists.intro (max (max N 2) M)
      (And.intro (le_max_left _ _) (hM _ (le_max_right _ _)))

theorem greedyDeletedPrimeClass_RH_real_count_sqrt_log_bigO
    (hRH : RiemannHypothesis) :
    Asymptotics.IsBigO atTop
      (fun X : Real =>
        ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor X)).card : Real))
      (fun X : Real => Real.sqrt X * Real.log X) := by
  choose C hC N hN using greedyDeletedPrimeClass_RH_eventually_count_sqrt_log hRH
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop ((max N 2 : Nat) : Real)] with X hX
  have hFloor : max N 2 <= Nat.floor X := Nat.le_floor hX
  have hTwo : 2 <= Nat.floor X := (le_max_right N 2).trans hFloor
  have hFloorPos : (0 : Real) < (Nat.floor X : Real) := by
    exact_mod_cast (by omega : 0 < Nat.floor X)
  have hFloorOne : (1 : Real) <= (Nat.floor X : Real) := by exact_mod_cast (by omega : 1 <= Nat.floor X)
  have hXTwo : (2 : Real) <= X := by
    have h := show (2 : Real) <= ((max N 2 : Nat) : Real) by exact_mod_cast (le_max_right N 2)
    exact h.trans hX
  have hFloorLe : (Nat.floor X : Real) <= X := Nat.floor_le (by linarith only [hXTwo])
  have hLog : Real.log (Nat.floor X : Real) <= Real.log X :=
    Real.log_le_log hFloorPos hFloorLe
  have hProduct := mul_le_mul (Real.sqrt_le_sqrt hFloorLe) hLog
    (Real.log_nonneg hFloorOne) (Real.sqrt_nonneg X)
  have hScaled := mul_le_mul_of_nonneg_left hProduct hC.le
  have hBound := hN (Nat.floor X) ((le_max_left N 2).trans hFloor)
  have hNonneg : 0 <= Real.sqrt X * Real.log X :=
    mul_nonneg (Real.sqrt_nonneg X) (Real.log_nonneg (by linarith only [hXTwo]))
  have hCard : (0 : Real) <=
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor X)).card : Real) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hCard, abs_of_nonneg hNonneg]
  nlinarith only [hBound, hScaled]

theorem riemannHypothesis_iff_greedyDeletedPrimeClass_real_count_bigO :
    RiemannHypothesis <->
      (forall epsilon : Real, 0 < epsilon ->
        Asymptotics.IsBigO atTop
          (fun X : Real =>
            ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor X)).card : Real))
          (fun X : Real => X ^ ((1 / 2 : Real) + epsilon))) := by
  constructor
  case mp =>
    intro hRH epsilon he
    exact primeClassPrefix_real_power_bigO_of_eventually_nat greedyDeletedPrimeClass
      ((1 / 2 : Real) + epsilon) (by linarith only [he])
      (greedyDeletedPrimeClass_eventually_power_count_of_RH hRH epsilon he)
  case mpr =>
    intro hCount
    apply riemannHypothesis_iff_cofinal_greedyDeletedPrimeClass_count.mpr
    intro epsilon he N
    have hEvent := primeClassPrefix_eventually_nat_power_of_real_power_bigO
      greedyDeletedPrimeClass ((1 / 2 : Real) + epsilon / 2) ((1 / 2 : Real) + epsilon)
      (by linarith only [he]) (hCount (epsilon / 2) (by linarith only [he]))
    choose M hM using Filter.eventually_atTop.mp hEvent
    exact Exists.intro (max (max N 2) M)
      (And.intro (le_max_left _ _) (hM _ (le_max_right _ _)))

end PrimeFactorOscillations.PrimeClassDeletion
