/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPositiveCover

/-!
# Wider fixed intervals for the actual prime-target source

Each cofactor branch uses one fixed interval and its complete source-error
packet. Ordered representations and diagonals are retained. The normalized
prime-pair supply is 63/1024; orbit entry remains a separate requirement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfWideScale (M r : Nat) : Nat := if r % 4 = 1 then M else M / 2
def lpfWideStart (m : Nat) : Nat := (m + 3) / 4
def lpfWideLength (m : Nat) : Nat := m - lpfWideStart m
def lpfWideInputs (m : Nat) : Finset Nat := Finset.Ioc (lpfWideStart m) m

theorem lpf_wide_interval_core (s m t : Nat) :
    Finset.Icc (max (s + 1) (t - m)) (min m (t - s - 1)) <=
      Finset.sumPartners (Finset.Ioc s m) t := by
  intro p hp
  have h := Finset.mem_Icc.mp hp
  have hLow := le_max_left (s + 1) (t - m)
  have hOther := le_max_right (s + 1) (t - m)
  have hHigh := min_le_left m (t - s - 1)
  have hBound := min_le_right m (t - s - 1)
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_Ioc.mpr (by omega)) ?_
  exact And.intro (Finset.mem_Ioc.mpr (by omega)) (by omega)

theorem lpf_wide_prime_pair_kernel (M r : Nat) (hM : 128 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) :
    M <= 8 * (Finset.sumPartners (lpfWideInputs (lpfWideScale M r))
      (primeTargetSum r)).card := by
  have hR := nextPrimeWindow_spec M r hr
  have hCard := Finset.card_le_card (lpf_wide_interval_core
    (lpfWideStart (lpfWideScale M r)) (lpfWideScale M r) (primeTargetSum r))
  rw [Nat.card_Icc] at hCard
  change min (lpfWideScale M r) (primeTargetSum r - lpfWideStart (lpfWideScale M r) - 1) + 1 -
    max (lpfWideStart (lpfWideScale M r) + 1) (primeTargetSum r - lpfWideScale M r) <=
      (Finset.sumPartners (lpfWideInputs (lpfWideScale M r)) (primeTargetSum r)).card at hCard
  unfold lpfWideScale lpfWideStart primeTargetSum at hCard
  unfold lpfWideScale primeTargetSum
  split_ifs at * <;> omega

theorem lpf_wide_scale_bounds (M r : Nat) :
    And (lpfWideScale M r <= M) (M <= 2 * lpfWideScale M r + 1) := by
  unfold lpfWideScale
  split_ifs <;> omega

theorem lpf_wide_physical (m : Nat) (hm : 1 <= m) :
    And ((m : Real) / 4 <= (lpfWideStart m : Real))
      (And (lpfWideStart m + lpfWideLength m = m) (lpfWideLength m <= m)) := by
  have hNat : m <= 4 * lpfWideStart m := by unfold lpfWideStart; omega
  have hCast : (m : Real) <= 4 * (lpfWideStart m : Real) := by exact_mod_cast hNat
  have hStart : lpfWideStart m <= m := by unfold lpfWideStart; omega
  exact And.intro (by linarith only [hCast]) (And.intro (by unfold lpfWideLength; omega)
    (Nat.sub_le _ _))

theorem lpf_wide_input_bounds (M r p : Nat)
    (hp : Membership.mem (Finset.sumPartners (lpfWideInputs (lpfWideScale M r))
      (primeTargetSum r)) p) :
    And (Membership.mem (Finset.Icc 1 M) p)
      (Membership.mem (Finset.Icc 1 M) (primeTargetSum r - p)) := by
  have h := Finset.mem_filter.mp hp
  have hP := Finset.mem_Ioc.mp h.1
  have hQ := Finset.mem_Ioc.mp h.2.1
  have hTop := (lpf_wide_scale_bounds M r).1
  exact And.intro (Finset.mem_Icc.mpr (by omega)) (Finset.mem_Icc.mpr (by omega))

theorem lpf_wide_target_pool (M r : Nat) (hM : 128 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) :
    Membership.mem (goldbachEvenTargets (lpfWideScale M r)) (primeTargetSum r) := by
  have h := primeTarget_goldbach_source_interval M r (by omega) hr
  unfold lpfWideScale
  split_ifs at * <;> assumption

theorem lpf_wide_bad_error {N : Nat} [NeZero N] (M r : Nat)
    (hM : 128 <= M) (hr : Membership.mem (nextPrimeWindow M) r) (hN : 4 * M < N)
    (hBad : lpfWeightedPartners (lpfWideInputs (lpfWideScale M r)) (primeTargetSum r) <
      (M : Real) * singularDivisorProduct (primeTargetSum r) / 16) :
    (M : Real) / 16 <= norm (lpfFixedSourceError N
      (lpfWideStart (lpfWideScale M r)) (lpfWideLength (lpfWideScale M r)) (primeTargetSum r)) := by
  let m := lpfWideScale M r
  let s := lpfWideStart m
  let L := lpfWideLength m
  let t := primeTargetSum r
  let A := Finset.Ioc s (s + L)
  have hmTop := (lpf_wide_scale_bounds M r).1
  have hmOne : 1 <= m := by dsimp [m, lpfWideScale]; split_ifs <;> omega
  have hGeom := lpf_wide_physical m hmOne
  have hEq : A = lpfWideInputs m := by
    change Finset.Ioc (lpfWideStart m) (lpfWideStart m + lpfWideLength m) = _
    rw [hGeom.2.1]
    rfl
  have htData := Finset.mem_Ioo.mp (Finset.mem_filter.mp (lpf_wide_target_pool M r hM hr)).1
  have htPos : 0 < t := by dsimp [t]; omega
  have hTN : t < N := by dsimp [t, m] at *; omega
  have hNoWrap : 2 * (s + L) < N := by
    change 2 * (lpfWideStart m + lpfWideLength m) < N
    rw [hGeom.2.1]
    change m <= M at hmTop
    omega
  have hKernel := lpf_wide_prime_pair_kernel M r hM hr
  have hKernelR : (M : Real) <= 8 * ((Finset.sumPartners A t).card : Real) := by
    rw [hEq]
    exact_mod_cast hKernel
  have hCard : (M : Real) / 8 <= ((Finset.sumPartners A t).card : Real) := by
    linarith only [hKernelR]
  have hR := nextPrimeWindow_spec M r hr
  have hEven : Dvd.dvd 2 t := Nat.dvd_of_mod_eq_zero
    (primeTargetSum_even r hR.1 (by omega))
  have hSeries := lpf_singular_series_re_lower_bound t htPos hEven
  have hG := sieve_singularDivisorProduct_one_le t
  have hMain := mul_le_mul hCard hSeries (zero_le_one.trans hG)
    (Nat.cast_nonneg ((Finset.sumPartners A t).card))
  have hFixed : (lpfCyclicInverse (fun x => lpfGridIntervalWeight N s L x ^ 2) (t : ZMod N)).re =
      lpfWeightedPartners A t := by
    rw [lpf_grid_interval_inverse_weighted s L t hNoWrap hTN, Complex.ofReal_re]
  have hRe : (lpfFixedSourceError N s L t).re = lpfWeightedPartners A t -
      ((Finset.sumPartners A t).card : Real) * (lpfSingularSeries t).re := by
    unfold lpfFixedSourceError
    rw [lpf_interval_pairCount_sumPartners s L t hNoWrap hTN]
    simp only [Complex.sub_re, Complex.mul_re]
    simp [A, hFixed]
  have hBadA : lpfWeightedPartners A t < (M : Real) * singularDivisorProduct t / 16 := by
    rw [hEq]
    exact hBad
  have hAllowance : (M : Real) / 16 <= (M : Real) / 16 * singularDivisorProduct t := by
    have h := mul_le_mul_of_nonneg_left hG (by positivity : 0 <= (M : Real) / 16)
    simpa only [mul_one] using h
  have hNorm : -(lpfFixedSourceError N s L t).re <= norm (lpfFixedSourceError N s L t) :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  change (M : Real) / 16 <= norm (lpfFixedSourceError N s L t)
  nlinarith only [hMain, hRe, hBadA, hAllowance, hNorm]

theorem lpf_wide_branch_bad_card_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M m : Nat) (R : Finset Nat),
        2 ^ 19 <= M -> m <= M -> M <= 2 * m + 1 -> Dvd.dvd m N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff m -> Dvd.dvd q N) -> 4 * M < N ->
        (forall r, Membership.mem R r -> And (Membership.mem (nextPrimeWindow M) r)
          (And (lpfWideScale M r = m)
            (lpfWeightedPartners (lpfWideInputs m) (primeTargetSum r) <
              (M : Real) * singularDivisorProduct (primeTargetSum r) / 16))) ->
        (R.card : Real) <= C * (M : Real) ^ (79 / 80 : Real)) := by
  classical
  choose A hA hBound using lpf_fixed_source_power_bound
  let C : Real := (16 : Real) ^ 2 * A
  refine Exists.intro C (And.intro (by dsimp [C]; positivity) ?_)
  intro N instN M m R hM hmTop hmHalf hDivM hDiv hN hTargets
  have hM128 : 128 <= M := (by decide : 128 <= 2 ^ 19).trans hM
  have hmWarm : 2 ^ 18 <= m := by norm_num at hM; norm_num; omega
  have hmOne : 1 <= m := (by decide : 1 <= 2 ^ 18).trans hmWarm
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  let T := R.image primeTargetSum
  have hInj : Set.InjOn primeTargetSum (R : Set Nat) := by
    intro r hr s hs hEq
    have hR := nextPrimeWindow_spec M r (hTargets r hr).1
    have hS := nextPrimeWindow_spec M s (hTargets s hs).1
    exact primeTarget_injective_window M r s (by omega) hR.1 hS.1 hR.2 hS.2 hEq
  have hImage : R.card = T.card := (Finset.card_image_of_injOn hInj).symm
  have hT (t : Nat) (ht : Membership.mem T t) : And (0 < t) (t <= 2 * m) := by
    choose r hr hEq using Finset.mem_image.mp ht
    have hData := hTargets r hr
    have hPool := lpf_wide_target_pool M r hM128 hData.1
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
  have hBudget := hBound m (lpfWideStart m) (lpfWideLength m) T
    hmWarm hDivM hDiv hPhysical.1 hTop hPhysical.2.2 hInput hOutput hT hCard
  have hPower : (m : Real) ^ (239 / 80 : Real) <= (M : Real) ^ (239 / 80 : Real) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmTop) (by norm_num)
  have hNorm (t : Nat) (ht : Membership.mem T t) : ((M : Real) / 16) ^ 2 <=
      norm (lpfFixedSourceError N (lpfWideStart m) (lpfWideLength m) t) ^ 2 := by
    choose r hr hEq using Finset.mem_image.mp ht
    have hData := hTargets r hr
    have hBad : lpfWeightedPartners (lpfWideInputs (lpfWideScale M r)) (primeTargetSum r) <
        (M : Real) * singularDivisorProduct (primeTargetSum r) / 16 := by
      rw [hData.2.1]
      exact hData.2.2
    have h := lpf_wide_bad_error M r hM128 hData.1 hN hBad
    rw [hData.2.1, hEq] at h
    simpa only [pow_two] using mul_le_mul h h
      (by positivity : 0 <= (M : Real) / 16) (norm_nonneg _)
  have hEnergy : (T.card : Real) * ((M : Real) / 16) ^ 2 <= A * (M : Real) ^ (239 / 80 : Real) := by
    calc
      _ = Finset.sum T (fun _ => ((M : Real) / 16) ^ 2) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= Finset.sum T (fun t => norm (lpfFixedSourceError N (lpfWideStart m) (lpfWideLength m) t) ^ 2) :=
        Finset.sum_le_sum hNorm
      _ <= A * (m : Real) ^ (239 / 80 : Real) := hBudget
      _ <= _ := mul_le_mul_of_nonneg_left hPower hA.le
  have hRpow : (M : Real) ^ (79 / 80 : Real) * (M : Real) ^ 2 =
      (M : Real) ^ (239 / 80 : Real) := by
    rw [<- Real.rpow_natCast (M : Real) 2, <- Real.rpow_add hMR]
    norm_num
  have hRight : (C * (M : Real) ^ (79 / 80 : Real)) * ((M : Real) / 16) ^ 2 =
      A * (M : Real) ^ (239 / 80 : Real) := by
    calc
      _ = A * ((M : Real) ^ (79 / 80 : Real) * (M : Real) ^ 2) := by dsimp [C]; ring
      _ = _ := by rw [hRpow]
  rw [hImage]
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < ((M : Real) / 16) ^ 2)).mp
  rw [hRight]
  exact hEnergy

noncomputable def lpfWideBadPrimeTargets (M : Nat) : Finset Nat :=
  (nextPrimeWindow M).filter (fun r =>
    lpfWeightedPartners (lpfWideInputs (lpfWideScale M r)) (primeTargetSum r) <
      (M : Real) * singularDivisorProduct (primeTargetSum r) / 16)

noncomputable def lpfWideBadBranch (M m : Nat) : Finset Nat :=
  (lpfWideBadPrimeTargets M).filter (fun r => lpfWideScale M r = m)

theorem lpf_wide_bad_prime_targets_card_bound :
    exists C : Real, And (0 < C) (forall M : Nat, 2 ^ 19 <= M ->
      ((lpfWideBadPrimeTargets M).card : Real) <= C * (M : Real) ^ (79 / 80 : Real)) := by
  classical
  choose C hC hSingle using lpf_wide_branch_bad_card_bound
  refine Exists.intro (2 * C) (And.intro (by positivity) ?_)
  intro M hM
  let N := lpfPositiveGrid M
  have hN : 4 * M < N := lpf_positive_grid_large M
  letI : NeZero N := NeZero.mk (by omega)
  have hMOne : 1 <= M := (by decide : 1 <= 2 ^ 19).trans hM
  have hBranch (m : Nat) (hmTop : m <= M) (hmHalf : M <= 2 * m + 1) :
      ((lpfWideBadBranch M m).card : Real) <= C * (M : Real) ^ (79 / 80 : Real) := by
    have hmOne : 1 <= m := by norm_num at hM; omega
    have hDivM : Dvd.dvd m N := lpf_positive_grid_divisible M m (by omega) hmTop
    have hDiv (q : Nat) (hq : 0 < q) (hqCut : q <= lpfSourceCutoff m) : Dvd.dvd q N :=
      lpf_positive_grid_divisible M q hq ((hqCut.trans (lpf_source_cutoff_le_self m hmOne)).trans hmTop)
    apply hSingle (N := N) M m (lpfWideBadBranch M m) hM hmTop hmHalf hDivM hDiv hN
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hRaw := Finset.mem_filter.mp h.1
    refine And.intro hRaw.1 (And.intro h.2 ?_)
    simpa only [h.2] using hRaw.2
  have hCover : lpfWideBadPrimeTargets M <=
      Union.union (lpfWideBadBranch M M) (lpfWideBadBranch M (M / 2)) := by
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
  have hCard : ((lpfWideBadPrimeTargets M).card : Real) <=
      ((lpfWideBadBranch M M).card : Real) + ((lpfWideBadBranch M (M / 2)).card : Real) := by
    exact_mod_cast (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hFull := hBranch M le_rfl (by omega)
  have hHalf := hBranch (M / 2) (Nat.div_le_self M 2) (by omega)
  nlinarith only [hCard, hFull, hHalf]

/-- Wider fixed input intervals improve the complete positive supply and keep
the same mean-square exponent. Entry of a generated orbit is still required. -/
theorem exists_wide_primeTarget_supply_power_explicit :
    exists C : Real, And (0 < C)
      (forall M : Nat, 2 ^ 44 <= M ->
        exists Z : Finset Nat, And ((Z.card : Real) <= C * (M : Real) ^ (79 / 80 : Real))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (63 / 1024 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real))) := by
  classical
  choose C hC hBad using lpf_wide_bad_prime_targets_card_bound
  refine Exists.intro C (And.intro hC ?_)
  intro M hM
  have hM19 : 2 ^ 19 <= M := (by decide : 2 ^ 19 <= 2 ^ 44).trans hM
  have hM2 : 2 <= M := (by decide : 2 <= 2 ^ 44).trans hM
  refine Exists.intro (lpfWideBadPrimeTargets M) (And.intro (hBad M hM19) ?_)
  intro r hr
  have hR := Finset.mem_sdiff.mp hr
  let m := lpfWideScale M r
  let t := primeTargetSum r
  let A := Finset.sumPartners (lpfWideInputs m) t
  have hGood : (M : Real) * singularDivisorProduct t / 16 <=
      lpfWeightedPartners (lpfWideInputs m) t := by
    apply le_of_not_gt
    intro hFail
    apply hR.2
    exact Finset.mem_filter.mpr (And.intro hR.1 hFail)
  have hSupply : (1 / 16 : Real) * (M : Real) * singularDivisorProduct t <=
      goldbachMangoldtWeight A t := by
    change (1 / 16 : Real) * (M : Real) * singularDivisorProduct t <=
      lpfWeightedPartners (lpfWideInputs m) t
    convert hGood using 1 <;> ring
  have hInput := fun p hp => (lpf_wide_input_bounds M r p hp).1
  have hPartner := fun p hp => (lpf_wide_input_bounds M r p hp).2
  have hLoss := (goldbach_primePower_difference_bound A M t (by omega) hInput hPartner).2
  have hSmall := goldbach_primePower_loss_explicit M hM
  have hRep := goldbachMangoldt_to_sumPartners_of_deficit
    (1 / 16 : Real) (1 / 1024 : Real) (by norm_num)
    M hM2 A t hInput hPartner (hLoss.trans hSmall) hSupply
  convert hRep using 1 <;> norm_num

/-- A smaller positive supply is already valid at the lower explicit cutoff. -/
theorem exists_wide_primeTarget_supply_low_cutoff :
    exists C : Real, And (0 < C)
      (forall M : Nat, 2 ^ 20 <= M ->
        exists Z : Finset Nat, And ((Z.card : Real) <= C * (M : Real) ^ (79 / 80 : Real))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            (1 / 256 : Real) * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real))) := by
  classical
  choose C hC hBad using lpf_wide_bad_prime_targets_card_bound
  refine Exists.intro C (And.intro hC ?_)
  intro M hM
  have hM19 : 2 ^ 19 <= M := (by decide : 2 ^ 19 <= 2 ^ 20).trans hM
  have hM2 : 2 <= M := (by decide : 2 <= 2 ^ 20).trans hM
  refine Exists.intro (lpfWideBadPrimeTargets M) (And.intro (hBad M hM19) ?_)
  intro r hr
  have hR := Finset.mem_sdiff.mp hr
  let m := lpfWideScale M r
  let t := primeTargetSum r
  let A := Finset.sumPartners (lpfWideInputs m) t
  have hGood : (M : Real) * singularDivisorProduct t / 16 <=
      lpfWeightedPartners (lpfWideInputs m) t := by
    apply le_of_not_gt
    intro hFail
    apply hR.2
    exact Finset.mem_filter.mpr (And.intro hR.1 hFail)
  have hSupply : (1 / 16 : Real) * (M : Real) * singularDivisorProduct t <=
      goldbachMangoldtWeight A t := by
    change (1 / 16 : Real) * (M : Real) * singularDivisorProduct t <=
      lpfWeightedPartners (lpfWideInputs m) t
    convert hGood using 1 <;> ring
  have hInput := fun p hp => (lpf_wide_input_bounds M r p hp).1
  have hPartner := fun p hp => (lpf_wide_input_bounds M r p hp).2
  have hLoss := (goldbach_primePower_difference_linear_bound A M t hM hInput hPartner).2
  have hSmall := primePower_linear_loss_explicit M hM
  have hRep := goldbachMangoldt_to_sumPartners_of_deficit
    (1 / 16 : Real) (15 / 256 : Real) (by norm_num)
    M hM2 A t hInput hPartner (hLoss.trans hSmall) hSupply
  convert hRep using 1 <;> norm_num

end PrimeFactorOscillations.LPF
