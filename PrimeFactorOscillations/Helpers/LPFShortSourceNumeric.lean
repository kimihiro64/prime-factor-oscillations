/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFullSourceNumeric
import PrimeFactorOscillations.Helpers.LPFShortSource

/-!
# Complete numerical short-window prime-pair supply

The complete four-packet source bound controls both cofactor branches. The
exceptional set has coefficient 2^117 and exponent 39/40 with logarithmic
power twelve. The prime-power losses and positive 67/1024 supply are retained.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_short_branch_bad_energy_numeric :
    forall {N : Nat} [NeZero N] (M m : Nat) (R : Finset Nat),
        2 ^ 20 <= M -> m <= M -> M <= 2 * m + 1 -> Dvd.dvd m N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff m -> Dvd.dvd q N) -> 4 * M < N ->
        (forall r, Membership.mem R r -> And (Membership.mem (lpfShortPrimeWindow M) r)
          (And (lpfWideScale M r = m)
            (lpfWeightedPartners (lpfWideInputs m) (primeTargetSum r) <
              (M : Real) * singularDivisorProduct (primeTargetSum r) * (127 / 1024 : Real)))) ->
        (R.card : Real) * ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
          (2 : Real) ^ (109 : Nat) * (M : Real) ^ (119 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12 := by
  classical
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
  have hSub : T <= Finset.Icc 1 (2 * m) := by
    intro t ht
    have h := hT t ht
    exact Finset.mem_Icc.mpr (by constructor <;> omega)
  have hCard : T.card <= 2 * m := by
    have h := Finset.card_le_card hSub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hPhysical := lpf_wide_physical m hmOne
  have hInput : lpfWideStart m + lpfWideLength m < N := by rw [hPhysical.2.1]; omega
  have hOutput : 2 * m < N := by omega
  have hTop : lpfWideStart m + lpfWideLength m <= 2 * m := by rw [hPhysical.2.1]; omega
  have hBudget := lpf_fixed_source_mean_log_power_numeric_coarse m (lpfWideStart m) (lpfWideLength m) T
    hmWarm hDivM hDiv hPhysical.1 hTop hPhysical.2.2 hInput hOutput hT
  have hPower : (m : Real) ^ (119 / 40 : Real) <= (M : Real) ^ (119 / 40 : Real) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmTop) (by norm_num)
  have hEll : And (0 <= 1 + Real.log (2 * (m : Real)))
      (1 + Real.log (2 * (m : Real)) <= 1 + Real.log (2 * (M : Real))) := by
    have hmR : (1 : Real) <= (m : Real) := by exact_mod_cast hmOne
    have hMR : (m : Real) <= (M : Real) := by exact_mod_cast hmTop
    have h0 := Real.log_nonneg (show 1 <= 2 * (m : Real) by linarith)
    have h1 := Real.log_le_log (show 0 < 2 * (m : Real) by linarith)
      (show 2 * (m : Real) <= 2 * (M : Real) by linarith)
    exact And.intro (by linarith) (by linarith)
  have hEllPower : (1 + Real.log (2 * (m : Real))) ^ (12 : Nat) <=
      (1 + Real.log (2 * (M : Real))) ^ (12 : Nat) := by
    rw [<- Real.rpow_natCast _ 12, <- Real.rpow_natCast _ 12]
    exact Real.rpow_le_rpow hEll.1 hEll.2 (by positivity)
  have hTotal := mul_le_mul hPower hEllPower (pow_nonneg hEll.1 12)
    (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hBudgetM : Finset.sum T (fun t =>
      norm (lpfFixedSourceError N (lpfWideStart m) (lpfWideLength m) t) ^ 2) <=
      (2 : Real) ^ (109 : Nat) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have hScaled := mul_le_mul_of_nonneg_left hTotal
      (show (0 : Real) <= (2 : Real) ^ (109 : Nat) by positivity)
    exact hBudget.trans (by convert hScaled using 1 <;> ring)
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
    _ <= _ := hBudgetM


theorem lpf_short_bad_prime_targets_card_numeric (M : Nat) (hM : 2 ^ 20 <= M) :
    ((lpfShortBadPrimeTargets M).card : Real) <=
      (2 : Real) ^ (117 : Nat) * (M : Real) ^ (39 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
  classical
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast (by norm_num at hM; omega : 0 < M)
  let N := lpfPositiveGrid M
  have hN : 4 * M < N := lpf_positive_grid_large M
  letI : NeZero N := NeZero.mk (by omega)
  have hBranch (m : Nat) (hmTop : m <= M) (hmHalf : M <= 2 * m + 1) :
      ((lpfShortBadBranch M m).card : Real) * ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
        (2 : Real) ^ (109 : Nat) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have hmOne : 1 <= m := by norm_num at hM; omega
    have hDivM : Dvd.dvd m N := lpf_positive_grid_divisible M m (by omega) hmTop
    have hDiv (q : Nat) (hq : 0 < q) (hqCut : q <= lpfSourceCutoff m) : Dvd.dvd q N :=
      lpf_positive_grid_divisible M q hq ((hqCut.trans (lpf_source_cutoff_le_self m hmOne)).trans hmTop)
    apply lpf_short_branch_bad_energy_numeric (N := N) M m (lpfShortBadBranch M m) hM hmTop hmHalf hDivM hDiv hN
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
  have hHalf := hBranch (M / 2) (Nat.div_le_self M 2) (by omega)
  have hEnergy : ((lpfShortBadPrimeTargets M).card : Real) *
      ((M : Real) * (127 / 1024 : Real)) ^ 2 <=
      (2 : Real) ^ (110 : Nat) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have h := mul_le_mul_of_nonneg_right hCard
      (sq_nonneg ((M : Real) * (127 / 1024 : Real)))
    have hC : (2 : Real) ^ (110 : Nat) = 2 * (2 : Real) ^ (109 : Nat) := by norm_num
    rw [hC]
    nlinarith only [h, hFull, hHalf]
  have hRpow : (M : Real) ^ (39 / 40 : Real) * (M : Real) ^ 2 =
      (M : Real) ^ (119 / 40 : Real) := by
    rw [<- Real.rpow_natCast (M : Real) 2, <- Real.rpow_add hMR]
    norm_num
  have hC : (2 : Real) ^ (110 : Nat) <=
      (2 : Real) ^ (117 : Nat) * (127 / 1024 : Real) ^ 2 := by norm_num
  have hRight :
      (2 : Real) ^ (110 : Nat) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 <=
      ((2 : Real) ^ (117 : Nat) * (M : Real) ^ (39 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12) *
          ((M : Real) * (127 / 1024 : Real)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hMR.le (119 / 40 : Real)))
      (by positivity : 0 <= (1 + Real.log (2 * (M : Real))) ^ (12 : Nat))
    calc
      _ <= ((2 : Real) ^ (117 : Nat) * (127 / 1024 : Real) ^ 2) *
          (M : Real) ^ (119 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12 := h
      _ = _ := by rw [<- hRpow]; ring
  apply (mul_le_mul_iff_of_pos_right
    (by positivity : 0 < ((M : Real) * (127 / 1024 : Real)) ^ 2)).mp
  exact hEnergy.trans hRight

theorem lpf_short_primeTarget_supply_numeric (M : Nat) (hM : 2 ^ 20 <= M) :
    exists Z : Finset Nat,
      And ((Z.card : Real) <=
        (2 : Real) ^ (117 : Nat) * (M : Real) ^ (39 / 40 : Real) *
          (1 + Real.log (2 * (M : Real))) ^ 12)
      (forall r, Membership.mem (SDiff.sdiff (lpfShortPrimeWindow M) Z) r ->
        (67 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
          (1 / singularDivisorProduct (primeTargetSum r)) *
            ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)) := by
  classical
  have hM2 : 2 <= M := (by decide : 2 <= 2 ^ 20).trans hM
  refine Exists.intro (lpfShortBadPrimeTargets M) (And.intro (lpf_short_bad_prime_targets_card_numeric M hM) ?_)
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

end PrimeFactorOscillations.LPF
