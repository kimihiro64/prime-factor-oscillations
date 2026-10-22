/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassPowerSummability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeStripCriterion
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeCountingZeroSupremum
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentStatistics

/-!
# The actual greedy deleted-prime component law

The arithmetic summability input is discharged from the actual zero
supremum and the proved strip/count transfer, including the critical case.
No RH assumption and no exact count-index limit are needed.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open Robin1984
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_powerWeight_summable_above_zeroSupremum
    (sigma : Real) (hSigma : actualZetaZeroSupremum < sigma) (hSigmaOne : sigma < 1) :
    Summable (classPowerWeight greedyDeletedPrimeClass sigma) := by
  have hSpec := actualZetaZeroSupremum_spec
  let eta : Real := (actualZetaZeroSupremum + sigma) / 2
  let a : Real := (eta + sigma) / 2
  have hEtaHalf : (1 / 2 : Real) <= eta := by
    dsimp only [eta]
    linarith only [hSpec.1, hSigma]
  have hEtaOne : eta < 1 := by
    dsimp only [eta]
    linarith only [hSigma, hSigmaOne]
  have hSupEta : actualZetaZeroSupremum <= eta := by
    dsimp only [eta]
    linarith only [hSigma]
  have hEtaA : eta < a := by
    dsimp only [a, eta]
    linarith only [hSigma]
  have hASigma : a < sigma := by
    dsimp only [a, eta]
    linarith only [hSigma]
  have ha0 : 0 <= a := by linarith only [hEtaHalf, hEtaA]
  have hs0 : 0 <= sigma := by linarith only [hSpec.1, hSigma]
  have hUpper (p : RiemannXiDivisorZeroIndex) :
      (riemannXiDivisorZeroValue p).re <= eta := by
    have hn := (riemannXi_zero_iff_nontrivial_zeta_zero
      (riemannXiDivisorZeroValue p)).mp (riemannXiDivisorZeroValue_eq_zero p)
    exact (hSpec.2.2 _ hn.1 hn.2).trans hSupEta
  have hcount := greedyDeletedPrimeClass_eventually_power_count_of_zero_strip
    eta hEtaHalf hEtaOne hUpper (a - eta) (sub_pos.mpr hEtaA)
  have he : eta + (a - eta) = a := by ring
  rw [he] at hcount
  choose N hN using Filter.eventually_atTop.mp hcount
  have hA : (1 : Real) <= (2 : Real) ^ a :=
    Real.one_le_rpow (by norm_num) ha0
  have hratio : (2 : Real) ^ a * (2 : Real) ^ (-sigma) < 1 := by
    rw [<- Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hASigma])
  apply classPowerWeight_summable_of_eventual_geometric_prefix_bound
    greedyDeletedPrimeClass 2 (by norm_num) sigma ((2 : Real) ^ a) ((2 : Real) ^ a)
    hs0 hA (Real.rpow_nonneg (by norm_num) _) hratio
  filter_upwards [eventually_ge_atTop N] with j hj
  have hNX : N <= 2 ^ (j + 1) := by
    have hpow := Nat.lt_two_pow_self (n := j + 1)
    omega
  have hraw := hN (2 ^ (j + 1)) hNX
  have hpower : (((2 ^ (j + 1) : Nat) : Real)) ^ a =
      (2 : Real) ^ a * ((2 : Real) ^ a) ^ j := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ = ((2 : Real) ^ ((j + 1 : Nat) : Real)) ^ a := by
        rw [Real.rpow_natCast]
      _ = (2 : Real) ^ (((j + 1 : Nat) : Real) * a) :=
        (Real.rpow_mul (by norm_num) ((j + 1 : Nat) : Real) a).symm
      _ = (2 : Real) ^ (a * ((j + 1 : Nat) : Real)) := by rw [mul_comm]
      _ = ((2 : Real) ^ a) ^ ((j + 1 : Nat) : Real) :=
        Real.rpow_mul (by norm_num) a ((j + 1 : Nat) : Real)
      _ = ((2 : Real) ^ a) ^ (j + 1) := Real.rpow_natCast _ (j + 1)
      _ = (2 : Real) ^ a * ((2 : Real) ^ a) ^ j := by rw [pow_succ, mul_comm]
  exact hraw.trans_eq hpower

theorem greedyDeletedPrimeClass_component_full_l1_error
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hSigma : actualZetaZeroSupremum < sigma) (hSigmaOne : sigma < 1) :
    And (Summable (fun a => abs
      (classPrimePowerComponentProbability greedyDeletedPrimeClass N a -
        classPrimePowerReference greedyDeletedPrimeClass a)))
      (tsum (fun a => abs
        (classPrimePowerComponentProbability greedyDeletedPrimeClass N a -
          classPrimePowerReference greedyDeletedPrimeClass a)) <=
        (N : Real) ^ (sigma - 1) *
          classPrimePowerErrorConstant greedyDeletedPrimeClass sigma) := by
  have hs : 0 < sigma := by
    linarith only [actualZetaZeroSupremum_spec.1, hSigma]
  exact classPrimePowerComponent_full_l1_error greedyDeletedPrimeClass N hN sigma hs
    hSigmaOne.le
    (greedyDeletedPrimeClass_powerWeight_summable_above_zeroSupremum sigma hSigma hSigmaOne)

theorem greedyDeletedPrimeClass_component_totalVariation_le
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hSigma : actualZetaZeroSupremum < sigma) (hSigmaOne : sigma < 1) :
    tsum (fun a => abs
      (classPrimePowerComponentProbability greedyDeletedPrimeClass N a -
        classPrimePowerReference greedyDeletedPrimeClass a)) / 2 <=
      min 1 ((N : Real) ^ (sigma - 1) *
        classPrimePowerErrorConstant greedyDeletedPrimeClass sigma / 2) := by
  have hs : 0 < sigma := by
    linarith only [actualZetaZeroSupremum_spec.1, hSigma]
  exact classPrimePowerComponent_totalVariation_le greedyDeletedPrimeClass N hN sigma hs
    hSigmaOne.le
    (greedyDeletedPrimeClass_powerWeight_summable_above_zeroSupremum sigma hSigma hSigmaOne)

theorem greedyDeletedPrimeClass_component_statistic_totalVariation_le {B : Type*}
    (f : Nat -> B) (N : Nat) (hN : 0 < N) (sigma : Real)
    (hSigma : actualZetaZeroSupremum < sigma) (hSigmaOne : sigma < 1) :
    tsum (fun b => abs
      (componentStatisticMass f
        (classPrimePowerComponentProbability greedyDeletedPrimeClass N) b -
        componentStatisticMass f (classPrimePowerReference greedyDeletedPrimeClass) b)) / 2 <=
      min 1 ((N : Real) ^ (sigma - 1) *
        classPrimePowerErrorConstant greedyDeletedPrimeClass sigma / 2) := by
  have hs : 0 < sigma := by
    linarith only [actualZetaZeroSupremum_spec.1, hSigma]
  exact classPrimePowerComponent_statistic_totalVariation_le f greedyDeletedPrimeClass
    N hN sigma hs hSigmaOne.le
    (greedyDeletedPrimeClass_powerWeight_summable_above_zeroSupremum sigma hSigma hSigmaOne)

end PrimeFactorOscillations.PrimeClassDeletion
