/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedSourceBudget
import PrimeFactorOscillations.Helpers.LPFShortLogSource

/-! Mean-source exceptional sets and conditional short-window transfer. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfMeanSourceCountConstant (K : Real) : Real :=
  (1024 / 127 : Real) ^ 2 * (1 + (1 / 2 : Real) ^ (119 / 40 : Real)) *
    (4 * (8 * K ^ 2 + 6 * K ^ 4 + 99906))

theorem lpf_short_branch_bad_mean_log_energy_probe :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M m : Nat) (R : Finset Nat),
        2 ^ 20 <= M -> m <= M -> M <= 2 * m + 1 -> Dvd.dvd m N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff m -> Dvd.dvd q N) -> 4 * M < N ->
        (forall r, Membership.mem R r -> And (Membership.mem (lpfShortPrimeWindow M) r)
          (And (lpfWideScale M r = m)
            (lpfWeightedPartners (lpfWideInputs m) (primeTargetSum r) <
              (M : Real) * singularDivisorProduct (primeTargetSum r) * (127 / 1024 : Real)))) ->
        (R.card : Real) * ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
          (4 * (8 * K ^ 2 + 6 * K ^ 4 + 99906)) * (m : Real) ^ (119 / 40 : Real) *
            (1 + Real.log (2 * (m : Real))) ^ 12) := by
  classical
  choose K hK hBound using lpf_fixed_source_mean_log_power_bound
  let A : Real := 4 * (8 * K ^ 2 + 6 * K ^ 4 + 99906)
  have hA : 0 < A := by dsimp [A]; positivity
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M m R hM hmTop hmHalf hDivM hDiv hN hTargets
  have hM128 : 128 <= M := (by decide : 128 <= 2 ^ 20).trans hM
  have hmWarm : 2 ^ 18 <= m := by norm_num at hM; norm_num; omega
  have hmOne : 1 <= m := (by decide : 1 <= 2 ^ 18).trans hmWarm
  let T := R.image primeTargetSum
  have hInj : Set.InjOn primeTargetSum (R : Set Nat) := by
    intro r hr s hs hEq
    have hR := nextPrimeWindow_spec M r (Finset.mem_filter.mp (hTargets r hr).1).1
    have hS := nextPrimeWindow_spec M s (Finset.mem_filter.mp (hTargets s hs).1).1
    exact primeTarget_injective_window M r s (by omega) hR.1 hS.1 hR.2 hS.2 hEq
  have hImage : R.card = T.card := (Finset.card_image_of_injOn hInj).symm
  have hT (t : Nat) (ht : Membership.mem T t) : And (0 < t) (t <= 2 * m) := by
    choose r hr hEq using Finset.mem_image.mp ht
    have hData := hTargets r hr
    have hPool := lpf_wide_target_pool M r hM128 (Finset.mem_filter.mp hData.1).1
    rw [hData.2.1] at hPool
    have h := Finset.mem_Ioo.mp (Finset.mem_filter.mp hPool).1
    rw [<- hEq]
    constructor <;> omega
  have hPhysical := lpf_wide_physical m hmOne
  have hInput : lpfWideStart m + lpfWideLength m < N := by rw [hPhysical.2.1]; omega
  have hOutput : 2 * m < N := by omega
  have hTop : lpfWideStart m + lpfWideLength m <= 2 * m := by rw [hPhysical.2.1]; omega
  have hBudget := hBound m (lpfWideStart m) (lpfWideLength m) T
    hmWarm hDivM hDiv hPhysical.1 hTop hPhysical.2.2 hInput hOutput hT
  have hNorm (t : Nat) (ht : Membership.mem T t) :
      ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
        norm (lpfFixedSourceError N (lpfWideStart m) (lpfWideLength m) t) ^ 2 := by
    choose r hr hEq using Finset.mem_image.mp ht
    have hData := hTargets r hr
    have hBad : lpfWeightedPartners (lpfWideInputs (lpfWideScale M r)) (primeTargetSum r) <
        (M : Real) * singularDivisorProduct (primeTargetSum r) * (127 / 1024 : Real) := by
      rw [hData.2.1]
      exact hData.2.2
    have h := lpf_short_bad_error M r hM hData.1 hN hBad
    rw [hData.2.1, hEq] at h
    simpa only [pow_two] using mul_le_mul h h
      (by positivity : 0 <= (M : Real) * (127 / 1024 : Real)) (norm_nonneg _)
  rw [hImage]
  calc
    _ = Finset.sum T (fun _ => ((M : Real) * (127 / 1024 : Real)) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= Finset.sum T (fun t =>
        norm (lpfFixedSourceError N (lpfWideStart m) (lpfWideLength m) t) ^ 2) :=
      Finset.sum_le_sum hNorm
    _ <= _ := hBudget

theorem lpf_short_half_mean_log_power_probe (M : Nat) (hM : 2 <= M) :
    ((M / 2 : Nat) : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * ((M / 2 : Nat) : Real))) ^ 12 <=
      (1 / 2 : Real) ^ (119 / 40 : Real) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
  have hHalfNat : 1 <= M / 2 := by omega
  have hHalfR : (1 : Real) <= ((M / 2 : Nat) : Real) := by exact_mod_cast hHalfNat
  have hHalfTop : ((M / 2 : Nat) : Real) <= (M : Real) :=
    Nat.cast_le.mpr (Nat.div_le_self M 2)
  have hLog : Real.log (2 * ((M / 2 : Nat) : Real)) <= Real.log (2 * (M : Real)) :=
    Real.log_le_log (by positivity) (by linarith only [hHalfTop])
  have hLog0 : 0 <= Real.log (2 * ((M / 2 : Nat) : Real)) :=
    Real.log_nonneg (by linarith only [hHalfR])
  have hPower := lpf_short_half_rpow_bound M (119 / 40) (by norm_num)
  have hLogPow : (1 + Real.log (2 * ((M / 2 : Nat) : Real))) ^ 12 <=
      (1 + Real.log (2 * (M : Real))) ^ 12 := by gcongr
  exact mul_le_mul hPower hLogPow (by positivity) (by positivity)

theorem lpf_short_bad_prime_targets_mean_log_card_bound_probe :
    exists K : Real, And (0 < K) (forall M : Nat, 2 ^ 20 <= M ->
      ((lpfShortBadPrimeTargets M).card : Real) <= lpfMeanSourceCountConstant K * (M : Real) ^ (39 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12) := by
  classical
  choose K hK hSingle using lpf_short_branch_bad_mean_log_energy_probe
  let A : Real := 4 * (8 * K ^ 2 + 6 * K ^ 4 + 99906)
  have hA : 0 < A := by dsimp [A]; positivity
  let C := (1024 / 127 : Real) ^ 2 *
    (1 + (1 / 2 : Real) ^ (119 / 40 : Real)) * A
  have hHalfPos := Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 1 / 2) (119 / 40 : Real)
  refine Exists.intro K (And.intro hK ?_)
  intro M hM
  change ((lpfShortBadPrimeTargets M).card : Real) <= C * (M : Real) ^ (39 / 40 : Real) *
    (1 + Real.log (2 * (M : Real))) ^ 12
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast (by norm_num at hM; omega : 0 < M)
  let N := lpfPositiveGrid M
  have hN : 4 * M < N := lpf_positive_grid_large M
  letI : NeZero N := NeZero.mk (by omega)
  have hBranch (m : Nat) (hmTop : m <= M) (hmHalf : M <= 2 * m + 1) :
      ((lpfShortBadBranch M m).card : Real) * ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
        A * (m : Real) ^ (119 / 40 : Real) *
          (1 + Real.log (2 * (m : Real))) ^ 12 := by
    have hmOne : 1 <= m := by norm_num at hM; omega
    have hDivM : Dvd.dvd m N := lpf_positive_grid_divisible M m (by omega) hmTop
    have hDiv (q : Nat) (hq : 0 < q) (hqCut : q <= lpfSourceCutoff m) : Dvd.dvd q N :=
      lpf_positive_grid_divisible M q hq ((hqCut.trans (lpf_source_cutoff_le_self m hmOne)).trans hmTop)
    apply hSingle (N := N) M m (lpfShortBadBranch M m) hM hmTop hmHalf hDivM hDiv hN
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hRaw := Finset.mem_filter.mp h.1
    refine And.intro hRaw.1 (And.intro h.2 ?_)
    simpa only [h.2] using hRaw.2
  have hCover : lpfShortBadPrimeTargets M <=
      Union.union (lpfShortBadBranch M M) (lpfShortBadBranch M (M / 2)) := by
    intro r hr
    by_cases hBranch : r % 4 = 1
    next =>
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact And.intro hr (by simp only [lpfWideScale, hBranch, ite_eq_left])
    next =>
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact And.intro hr (by simp [lpfWideScale, hBranch])
  have hCard : ((lpfShortBadPrimeTargets M).card : Real) <=
      ((lpfShortBadBranch M M).card : Real) + ((lpfShortBadBranch M (M / 2)).card : Real) := by
    exact_mod_cast (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFull := hBranch M le_rfl (by omega)
  have hHalfScaled := mul_le_mul_of_nonneg_left
    (lpf_short_half_mean_log_power_probe M (by omega)) hA.le
  have hHalf := (hBranch (M / 2) (Nat.div_le_self M 2) (by omega)).trans
    (by simpa only [mul_assoc] using hHalfScaled)
  have hEnergy : ((lpfShortBadPrimeTargets M).card : Real) *
      ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
        A * (1 + (1 / 2 : Real) ^ (119 / 40 : Real)) * (M : Real) ^ (119 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have h := mul_le_mul_of_nonneg_right hCard
      (sq_nonneg ((M : Real) * (127 / 1024 : Real)))
    nlinarith only [h, hFull, hHalf]
  have hRpow : (M : Real) ^ (39 / 40 : Real) * (M : Real) ^ 2 =
      (M : Real) ^ (119 / 40 : Real) := by
    rw [<- Real.rpow_natCast (M : Real) 2, <- Real.rpow_add hMR]
    norm_num
  have hRight : (C * (M : Real) ^ (39 / 40 : Real) *
      (1 + Real.log (2 * (M : Real))) ^ 12) *
      ((M : Real) * (127 / 1024 : Real)) ^ 2 =
        A * (1 + (1 / 2 : Real) ^ (119 / 40 : Real)) * (M : Real) ^ (119 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12 := by
    calc
      _ = A * (1 + (1 / 2 : Real) ^ (119 / 40 : Real)) *
          ((M : Real) ^ (39 / 40 : Real) * (M : Real) ^ 2) *
          (1 + Real.log (2 * (M : Real))) ^ 12 := by dsimp [C]; ring
      _ = _ := by rw [hRpow]
  apply (mul_le_mul_iff_of_pos_right
    (by positivity : 0 < ((M : Real) * (127 / 1024 : Real)) ^ 2)).mp
  rw [hRight]
  exact hEnergy

theorem exists_short_primeTarget_mean_log_supply_probe :
    exists K : Real, And (0 < K)
      (forall M : Nat, 2 ^ 20 <= M ->
        exists Z : Finset Nat, And ((Z.card : Real) <= lpfMeanSourceCountConstant K * (M : Real) ^ (39 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12)
          (forall r, Membership.mem (SDiff.sdiff (lpfShortPrimeWindow M) Z) r ->
            (67 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real))) := by
  classical
  choose K hK hBad using lpf_short_bad_prime_targets_mean_log_card_bound_probe
  refine Exists.intro K (And.intro hK ?_)
  intro M hM
  have hM2 : 2 <= M := (by decide : 2 <= 2 ^ 20).trans hM
  refine Exists.intro (lpfShortBadPrimeTargets M) (And.intro (hBad M hM) ?_)
  intro r hr
  have hR := Finset.mem_sdiff.mp hr
  let m := lpfWideScale M r
  let t := primeTargetSum r
  let A := Finset.sumPartners (lpfWideInputs m) t
  have hGood : (M : Real) * singularDivisorProduct t * (127 / 1024 : Real) <=
      lpfWeightedPartners (lpfWideInputs m) t := by
    apply le_of_not_gt
    intro hFail
    apply hR.2
    exact Finset.mem_filter.mpr (And.intro hR.1 hFail)
  have hSupply : (127 / 1024 : Real) * (M : Real) * singularDivisorProduct t <=
      goldbachMangoldtWeight A t := by
    change (127 / 1024 : Real) * (M : Real) * singularDivisorProduct t <=
      lpfWeightedPartners (lpfWideInputs m) t
    convert hGood using 1 <;> ring
  have hInput := fun p hp => (lpf_wide_input_bounds M r p hp).1
  have hPartner := fun p hp => (lpf_wide_input_bounds M r p hp).2
  have hLoss := (goldbach_primePower_difference_linear_bound A M t hM hInput hPartner).2
  have hSmall := primePower_linear_loss_explicit M hM
  have hRep := goldbachMangoldt_to_sumPartners_of_deficit
    (127 / 1024 : Real) (15 / 256 : Real) (by norm_num)
    M hM2 A t hInput hPartner (hLoss.trans hSmall) hSupply
  convert hRep using 1 <;> norm_num

theorem exists_fullStep_dense_short_normalized_mean_log_bound_probe :
    exists K eta : Real, And (0 < K) (And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := ((SDiff.sdiff (inputPrimePrefix M) S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + lpfMeanSourceCountConstant K * (M : Real) ^ (39 / 40 : Real) *
            (1 + Real.log (2 * (M : Real))) ^ 12 +
            (8192 / 67 : Real) * eta * Real.log (M : Real))
        Filter.atTop)) := by
  choose K hK hSupply using exists_short_primeTarget_mean_log_supply_probe
  choose eta hEta hRec using exists_dense_fullStep_subwindow_row_normalized_recurrence
    (67 / 1024 : Real) (by norm_num)
  refine Exists.intro K (Exists.intro eta (And.intro hK (And.intro hEta ?_)))
  filter_upwards [hRec, Filter.eventually_ge_atTop (2 ^ 20 : Nat)] with M hStep hM
  intro S
  dsimp only
  intro hE
  choose Z hZ hGood using hSupply M hM
  have h := hStep (7 * M / 6) (by omega) S Z hE hGood
  have hCoeff : 8 * eta / (67 / 1024 : Real) = (8192 / 67 : Real) * eta := by ring
  rw [hCoeff] at h
  nlinarith only [h, hZ]


end PrimeFactorOscillations.LPF
