/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedCorrections
import PrimeFactorOscillations.Helpers.LPFAveragedSourceBudget
import PrimeFactorOscillations.Helpers.LPFDenseIteration
import PrimeFactorOscillations.Helpers.LPFMinorEnergyPower
import PrimeFactorOscillations.Helpers.LPFNumericalPreservation
import PrimeFactorOscillations.Helpers.LPFOverlapFullNumeric
import PrimeFactorOscillations.Helpers.LPFResidueCountsNumeric
import PrimeFactorOscillations.Helpers.LPFRowNormalization
import PrimeFactorOscillations.Helpers.LPFShortLogSource
import PrimeFactorOscillations.Helpers.LPFShortSourceNumeric
import PrimeFactorOscillations.Helpers.LPFSubwindowNumeric
import PrimeFactorOscillations.Helpers.LPFWideSource

/-!
# Positive prime-pair supply and dense-seed propagation

The complete fixed-cover bound supplies a positive normalized prime-pair count
outside a power-saving exceptional set. The analytic representation premise
of the dense recurrence is discharged. Entry of the orbit from two remains
an explicit unproved target; diagonals are retained at every generation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfPositiveBadPrimeTargets (M : Nat) : Finset Nat :=
  (nextPrimeWindow M).filter (fun r => Membership.mem (lpfBadSourceTargets M) (primeTargetSum r))

theorem lpf_positive_bad_prime_card_le (M : Nat) (hM : 128 <= M) :
    (lpfPositiveBadPrimeTargets M).card <= (lpfBadSourceTargets M).card := by
  classical
  let Z := lpfPositiveBadPrimeTargets M
  have hInj : Set.InjOn primeTargetSum (Z : Set Nat) := by
    intro r hr s hs hEq
    have hR := nextPrimeWindow_spec M r (Finset.mem_filter.mp hr).1
    have hS := nextPrimeWindow_spec M s (Finset.mem_filter.mp hs).1
    exact primeTarget_injective_window M r s (by omega) hR.1 hS.1 hR.2 hS.2 hEq
  have hImage : Z.image primeTargetSum <= lpfBadSourceTargets M := by
    intro t ht
    choose r hr hEq using Finset.mem_image.mp ht
    rw [<- hEq]
    exact (Finset.mem_filter.mp hr).2
  calc
    _ = (Z.image primeTargetSum).card := (Finset.card_image_of_injOn hInj).symm
    _ <= _ := Finset.card_le_card hImage

theorem lpf_positive_good_prime_weight (M r : Nat) (hM : 128 <= M)
    (hr : Membership.mem (SDiff.sdiff (nextPrimeWindow M) (lpfPositiveBadPrimeTargets M)) r) :
    (1 / 512 : Real) * (M : Real) * singularDivisorProduct (primeTargetSum r) <=
      goldbachMangoldtWeight (goldbachWindowInputs M (primeTargetSum r)) (primeTargetSum r) := by
  classical
  have hR := Finset.mem_sdiff.mp hr
  have hTarget := primeTarget_goldbach_source_interval M r (by omega) hR.1
  have hPool : Membership.mem (Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M))
      (primeTargetSum r) := by
    by_cases hBranch : r % 4 = 1
    next =>
      simp [hBranch] at hTarget
      exact Finset.mem_union_right _ hTarget
    next =>
      simp [hBranch] at hTarget
      exact Finset.mem_union_left _ hTarget
  have hGood : Not (Membership.mem (lpfBadSourceTargets M) (primeTargetSum r)) := by
    intro hBad
    exact hR.2 (Finset.mem_filter.mpr (And.intro hR.1 hBad))
  convert lpf_good_source_target_weight M (primeTargetSum r) hPool hGood using 1 <;> ring

theorem exists_primeTarget_supply_power_explicit :
    exists C : Real, And (0 < C)
      (forall M : Nat, 2 ^ 44 <= M ->
        exists Z : Finset Nat, And ((Z.card : Real) <= C * (M : Real) ^ (79 / 80 : Real))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (1 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
       := by
  classical
  choose C hC hBad using lpf_bad_source_targets_card_bound
  refine Exists.intro C (And.intro hC ?_)
  intro M hM
  have hM19 : 2 ^ 19 <= M := (by decide : 2 ^ 19 <= 2 ^ 44).trans hM
  have hM128 : 128 <= M := (by decide : 128 <= 2 ^ 44).trans hM
  have hSmall : 4 * Real.sqrt (M : Real) * Real.log (M : Real) ^ 2 <=
      ((1 / 512 : Real) / 2) * (M : Real) := by
    convert goldbach_primePower_loss_explicit M hM using 1 <;> norm_num
  have hConvert := goldbachMangoldt_to_sumPartners_of_loss (1 / 512 : Real)
    (by norm_num) M (by omega) hSmall
  refine Exists.intro (lpfPositiveBadPrimeTargets M) (And.intro ?_ ?_)
  next =>
    have hCard : ((lpfPositiveBadPrimeTargets M).card : Real) <= ((lpfBadSourceTargets M).card : Real) := by
      exact_mod_cast lpf_positive_bad_prime_card_le M hM128
    exact hCard.trans (hBad M hM19)
  next =>
    intro r hr
    have hR := (Finset.mem_sdiff.mp hr).1
    have hSupply := lpf_positive_good_prime_weight M r hM128 hr
    have hRep := hConvert (goldbachWindowInputs M (primeTargetSum r)) (primeTargetSum r)
      (fun p hp => (primeTarget_goldbach_input_bounds M r hM128 hR p hp).1)
      (fun p hp => (primeTarget_goldbach_input_bounds M r hM128 hR p hp).2) hSupply
    have hConstant : (1 / 512 : Real) / 2 = 1 / 1024 := by norm_num
    rw [hConstant] at hRep
    exact hRep

theorem exists_primeTarget_supply_power :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat =>
        exists Z : Finset Nat, And ((Z.card : Real) <= C * (M : Real) ^ (79 / 80 : Real))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (1 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
        Filter.atTop) := by
  choose C hC hSupply using exists_primeTarget_supply_power_explicit
  refine Exists.intro C (And.intro hC ?_)
  exact Filter.eventually_atTop.mpr (Exists.intro (2 ^ 44) hSupply)

theorem lpf_source_power_to_log_exception (M : Nat) (hM : 2 <= M) :
    (M : Real) ^ (79 / 80 : Real) <=
      (1442 : Real) ^ 9 * ((M : Real) / Real.log (M : Real) ^ 4) := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast (by omega : 1 <= M)
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hLog : 0 < Real.log (M : Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hLog4 : Real.log (M : Real) ^ 4 <=
      (1442 : Real) ^ 9 * (M : Real) ^ ((1 : Real) / 160) := by
    calc
      _ <= (1 + Real.log (M : Real)) ^ 4 := by gcongr <;> linarith
      _ <= (1 + Real.log (2 * (M : Real))) ^ 9 := lpf_source_log_power_le_nine M 4 (by omega) (by decide)
      _ <= _ := lpf_source_log_absorption M (by omega)
  have hPower : (M : Real) ^ (79 / 80 : Real) * (M : Real) ^ ((1 : Real) / 160) <= (M : Real) := by
    rw [<- Real.rpow_add hPos]
    norm_num
    have h := Real.rpow_le_rpow_of_exponent_le hMR (show (159 / 160 : Real) <= 1 by norm_num)
    simpa using h
  apply (mul_le_mul_iff_of_pos_right (pow_pos hLog 4)).mp
  have hRight : ((1442 : Real) ^ 9 * ((M : Real) / Real.log (M : Real) ^ 4)) *
      Real.log (M : Real) ^ 4 = (1442 : Real) ^ 9 * (M : Real) := by field_simp
  rw [hRight]
  calc
    _ <= (M : Real) ^ (79 / 80 : Real) *
        ((1442 : Real) ^ 9 * (M : Real) ^ ((1 : Real) / 160)) :=
      mul_le_mul_of_nonneg_left hLog4 (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = (1442 : Real) ^ 9 * ((M : Real) ^ (79 / 80 : Real) * (M : Real) ^ ((1 : Real) / 160)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left hPower (by positivity)

theorem exists_primeTarget_supply_log :
    exists C : Real, And (0 <= C)
      (Filter.Eventually (fun M : Nat =>
        exists Z : Finset Nat, And ((Z.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 4))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (1 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
        Filter.atTop) := by
  choose C hC hSupply using exists_primeTarget_supply_power
  refine Exists.intro (C * (1442 : Real) ^ 9) (And.intro (by positivity) ?_)
  filter_upwards [hSupply, Filter.eventually_ge_atTop (2 : Nat)] with M hRep hM
  choose Z hZ hGood using hRep
  refine Exists.intro Z (And.intro ?_ hGood)
  calc
    _ <= C * (M : Real) ^ (79 / 80 : Real) := hZ
    _ <= C * ((1442 : Real) ^ 9 * ((M : Real) / Real.log (M : Real) ^ 4)) :=
      mul_le_mul_of_nonneg_left (lpf_source_power_to_log_exception M hM) hC.le
    _ = _ := by ring

theorem exists_wide_primeTarget_supply_log :
    exists C : Real, And (0 <= C)
      (Filter.Eventually (fun M : Nat =>
        exists Z : Finset Nat, And ((Z.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 4))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (63 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
        Filter.atTop) := by
  choose C hC hSupplyAll using exists_wide_primeTarget_supply_power_explicit
  have hSupply : Filter.Eventually (fun M : Nat =>
      exists Z : Finset Nat, And ((Z.card : Real) <= C * (M : Real) ^ (79 / 80 : Real))
        (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
          (63 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
            (1 / singularDivisorProduct (primeTargetSum r)) *
              ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
      Filter.atTop := Filter.eventually_atTop.mpr (Exists.intro (2 ^ 44) hSupplyAll)
  refine Exists.intro (C * (1442 : Real) ^ 9) (And.intro (by positivity) ?_)
  filter_upwards [hSupply, Filter.eventually_ge_atTop (2 : Nat)] with M hRep hM
  choose Z hZ hGood using hRep
  refine Exists.intro Z (And.intro ?_ hGood)
  calc
    _ <= C * (M : Real) ^ (79 / 80 : Real) := hZ
    _ <= C * ((1442 : Real) ^ 9 * ((M : Real) / Real.log (M : Real) ^ 4)) :=
      mul_le_mul_of_nonneg_left (lpf_source_power_to_log_exception M hM) hC.le
    _ = _ := by ring

/-- Exact representation-degree normalization removes the diagonal upper-sieve
constant. The source exception and cross-overlap absorption are retained. -/
theorem exists_fullStep_dense_normalized_power_log_bound :
    exists C eta : Real, And (0 < C) (And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := ((SDiff.sdiff (inputPrimePrefix M) S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + C * (M : Real) ^ (79 / 80 : Real) +
            (8192 / 63 : Real) * eta * Real.log (M : Real))
        Filter.atTop)) := by
  choose C hC hSupply using exists_wide_primeTarget_supply_power_explicit
  choose eta hEta hRec using exists_dense_fullStep_prefix_row_normalized_recurrence
    (63 / 1024 : Real) (by norm_num)
  refine Exists.intro C (Exists.intro eta (And.intro hC (And.intro hEta ?_)))
  filter_upwards [hRec, Filter.eventually_ge_atTop (2 ^ 44 : Nat)] with M hStep hM
  intro S
  dsimp only
  intro hE
  choose Z hZ hGood using hSupply M hM
  have h := hStep S Z hE hGood
  have hCoeff : 8 * eta / (63 / 1024 : Real) = (8192 / 63 : Real) * eta := by ring
  rw [hCoeff] at h
  nlinarith only [h, hZ]

/-- Complete one-step bound with the small-target floor absorbed into the
existing defect. Only the source power error and a logarithmic remainder remain. -/
theorem exists_fullStep_dense_power_log_bound_from_wide_source :
    exists C D eta : Real, And (0 < C) (And (0 < D) (And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := ((SDiff.sdiff (inputPrimePrefix M) S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + C * (M : Real) ^ (79 / 80 : Real) +
            D * Real.log (M : Real))
        Filter.atTop))) := by
  choose C hC hSupply using exists_wide_primeTarget_supply_power_explicit
  choose eta D hEta hD hRec using exists_dense_fullStep_prefix_log_recurrence
    (63 / 1024 : Real) (by norm_num)
  refine Exists.intro C (Exists.intro D (Exists.intro eta
    (And.intro hC (And.intro hD (And.intro hEta ?_)))))
  filter_upwards [hRec, Filter.eventually_ge_atTop (2 ^ 44 : Nat)] with M hStep hM
  intro S
  dsimp only
  intro hE
  choose Z hZ hGood using hSupply M hM
  have h := hStep S Z hE hGood
  nlinarith only [h, hZ]

/-- Complete one-step bound retaining the source power error directly.
The residual M/log(M)^4 required by the installed deletion estimate remains. -/
theorem exists_fullStep_dense_power_bound_from_wide_source :
    exists C : Real, And (0 < C) (exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := ((SDiff.sdiff (inputPrimePrefix M) S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + C * (M : Real) ^ (79 / 80 : Real) +
            (M : Real) / Real.log (M : Real) ^ 4)
        Filter.atTop)) := by
  choose C hC hSupply using exists_wide_primeTarget_supply_power_explicit
  choose eta hEta hRec using exists_dense_fullStep_prefix_recurrence
    (63 / 1024 : Real) (by norm_num)
  refine Exists.intro C (And.intro hC (Exists.intro eta (And.intro hEta ?_)))
  filter_upwards [hRec, Filter.eventually_ge_atTop (2 ^ 44 : Nat)] with M hStep hM
  intro S
  dsimp only
  intro hE
  choose Z hZ hGood using hSupply M hM
  have h := hStep S Z hE hGood
  nlinarith only [h, hZ]

/-- The analytic representation premise is discharged; dense entry remains explicit. -/
theorem exists_fullOrbit_dense_bounds_from_positive_source :
    exists C : Real, And (0 <= C) (exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := fun j => ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j))
          (fullOrbit S j)).card : Real)
        let N := fun j => ((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real)
        let F := fun j => ((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real) ^ 4
        E 0 <= eta * N 0 ->
        And (forall j, E j <= eta * N j)
          (forall j, E j <= (17 / 16 : Real) ^ j * E 0 + 16 * (C + 1) * F j))
        Filter.atTop)) := by
  choose C hC hSupply using exists_wide_primeTarget_supply_log
  exact Exists.intro C (And.intro hC
    (exists_fullOrbit_dense_defect_bounds (63 / 1024 : Real) C (by norm_num) hC hSupply))

end PrimeFactorOscillations.LPF
