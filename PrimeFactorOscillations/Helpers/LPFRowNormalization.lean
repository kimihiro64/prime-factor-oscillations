/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDenseTransfer

/-!
# Exact representation-degree normalization

The complete proved recurrence retains the source exception term:
E_next <= 17*E/16 + |Z| + (8*eta/a)*log M.
The previous logarithmic coefficient is 8*C2*eta/a^2.
The joint cross-overlap allowance and its a^2 absorption remain unchanged.
Actual entry from {2} remains a separate, unproved target.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def primeTargetRowNormalizer (P : Finset Nat) (r : Nat) : Real :=
  1 / ((Finset.sumPartners P (primeTargetSum r)).card : Real)

theorem primeTargetWeight_self_exact (P : Finset Nat) (v : Nat -> Real) (r : Nat) :
    Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) =
      ((Finset.sumPartners P (primeTargetSum r)).card : Real) * v r ^ 2 := by
  classical
  let R := Finset.sumPartners P (primeTargetSum r)
  have hSubset : R <= P := fun p hp => (Finset.mem_filter.mp hp).1
  have hFilter : P.filter (fun p => Membership.mem R p) = R := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    next => intro h; exact h.2
    next => intro h; exact And.intro (hSubset h) h
  have hPoint : Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) =
      Finset.sum P (fun p => if Membership.mem R p then v r ^ 2 else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    change (if Membership.mem R p then v r else 0) ^ 2 =
      (if Membership.mem R p then v r ^ 2 else 0)
    by_cases h : Membership.mem R p <;> simp [h]
  rw [hPoint, <- Finset.sum_filter, hFilter]
  simp only [Finset.sum_const, nsmul_eq_mul, R]

theorem primeTarget_normalized_self_upper (P : Finset Nat) (r : Nat) (L : Real)
    (hL : 0 < L)
    (hLower : L <= ((Finset.sumPartners P (primeTargetSum r)).card : Real)) :
    Finset.sum P (fun p => primeTargetWeight P (primeTargetRowNormalizer P) p r ^ 2) <= 1 / L := by
  have hR : 0 < ((Finset.sumPartners P (primeTargetSum r)).card : Real) := hL.trans_le hLower
  rw [primeTargetWeight_self_exact]
  dsimp [primeTargetRowNormalizer]
  have hEq : ((Finset.sumPartners P (primeTargetSum r)).card : Real) *
      (1 / ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ^ 2 =
        1 / ((Finset.sumPartners P (primeTargetSum r)).card : Real) := by
    field_simp [ne_of_gt hR] <;> ring
  rw [hEq]
  exact one_div_le_one_div_of_le hL hLower

theorem primeTarget_normalized_row_eq (P : Finset Nat) (v : Nat -> Real) (p r : Nat)
    (hRow : 0 < v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)) :
    primeTargetWeight P (primeTargetRowNormalizer P) p r =
      (1 / (v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real))) *
        primeTargetWeight P v p r := by
  have hNe : Not (v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real) = 0) := ne_of_gt hRow
  have hFactors := mul_ne_zero_iff.mp hNe
  by_cases hp : Membership.mem (Finset.sumPartners P (primeTargetSum r)) p
  next =>
    simp [primeTargetWeight, hp, primeTargetRowNormalizer] <;>
      field_simp [hFactors.1, hFactors.2]
  next => simp [primeTargetWeight, hp]

theorem primeTarget_normalized_cross_upper (P : Finset Nat) (v : Nat -> Real)
    (r s : Nat) (L K : Real) (hL : 0 < L) (hK : 0 <= K)
    (hR : L <= v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real))
    (hS : L <= v s * ((Finset.sumPartners P (primeTargetSum s)).card : Real))
    (hCross : Finset.sum P (fun p =>
      primeTargetWeight P v p r * primeTargetWeight P v p s) <= K) :
    Finset.sum P (fun p =>
      primeTargetWeight P (primeTargetRowNormalizer P) p r *
        primeTargetWeight P (primeTargetRowNormalizer P) p s) <= K / L ^ 2 := by
  let R := v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)
  let S := v s * ((Finset.sumPartners P (primeTargetSum s)).card : Real)
  have hRp : 0 < R := hL.trans_le hR
  have hSp : 0 < S := hL.trans_le hS
  have hProd : L ^ 2 <= R * S := by
    have h := mul_le_mul hR hS hL.le hRp.le
    simpa only [pow_two] using h
  have hInv : 1 / (R * S) <= 1 / L ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hL 2) hProd
  have hSum : Finset.sum P (fun p =>
      primeTargetWeight P (primeTargetRowNormalizer P) p r *
        primeTargetWeight P (primeTargetRowNormalizer P) p s) =
      (1 / (R * S)) * Finset.sum P (fun p =>
        primeTargetWeight P v p r * primeTargetWeight P v p s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [primeTarget_normalized_row_eq P v p r hRp,
      primeTarget_normalized_row_eq P v p s hSp]
    dsimp [R, S]
    field_simp <;> ring
  rw [hSum]
  calc
    _ <= (1 / (R * S)) * K :=
      mul_le_mul_of_nonneg_left hCross (by positivity)
    _ <= (1 / L ^ 2) * K := mul_le_mul_of_nonneg_right hInv hK
    _ = K / L ^ 2 := by ring

theorem small_target_floor_absorbed_under_density (X ell a eta E : Real)
    (hX : 0 < X) (hell : 0 < ell) (ha : 0 < a) (hEta : 0 <= eta) (hE0 : 0 <= E)
    (hEtaA : 64 * eta <= a) (hEtaSq : 64 * eta <= a ^ 2)
    (hE : E <= eta * (X / ell)) (hRep : a * (X / ell ^ 2) <= 2 * E) :
    X / ell ^ 4 <= E / 16 := by
  have hScale : 32 <= a * ell ^ 2 := by
    by_contra h
    have hFail : a * ell ^ 2 < 32 := lt_of_not_ge h
    have hSource := mul_le_mul_of_nonneg_right hRep (sq_nonneg ell)
    have hCancel : (a * (X / ell ^ 2)) * ell ^ 2 = a * X := by
      field_simp [ne_of_gt hell]
    rw [hCancel] at hSource
    have hCapped := mul_le_mul_of_nonneg_right hE
      (by positivity : 0 <= 2 * ell ^ 2)
    have hCapCancel : (eta * (X / ell)) * (2 * ell ^ 2) = 2 * eta * ell * X := by
      field_simp [ne_of_gt hell]
    rw [hCapCancel] at hCapped
    have hCompare : a <= 2 * eta * ell := by
      apply (mul_le_mul_iff_of_pos_right hX).mp
      nlinarith only [hSource, hCapped]
    have hSquared : a ^ 2 <= (2 * eta * ell) ^ 2 := by
      have h := mul_le_mul hCompare hCompare ha.le (by positivity)
      simpa only [pow_two] using h
    have hProduct := mul_le_mul hEtaA hEtaSq (by positivity : 0 <= 64 * eta) ha.le
    have hProductScaled := mul_le_mul_of_nonneg_right hProduct (sq_nonneg ell)
    have hFailScaled := mul_lt_mul_of_pos_left hFail (pow_pos ha 2)
    nlinarith only [hSquared, hProductScaled, hFailScaled, sq_nonneg a]
  exact small_target_floor_absorbed X ell a E ha hell hE0 hRep hScale

private theorem absorption_scaled (a K eta : Real)
    (hAbs : forall d z : Real, 0 < d -> d <= eta -> 1 <= z -> z <= 16 / d ->
      8 * d * K * Real.log (3 + Real.log z) <= a ^ 2)
    (X ell E b : Real) (hX : 0 < X) (hell : 0 < ell) (hE : 0 < E)
    (hSmall : E <= eta * (X / ell)) (hb : E / 16 <= b)
    (hbN : b <= X / ell) :
    8 * E * ((K * X / ell ^ 3) * Real.log (3 + Real.log ((X / ell) / b))) <=
      (a * X / ell ^ 2) ^ 2 := by
  let N := X / ell
  have hN : 0 < N := div_pos hX hell
  have hbPos : 0 < b := lt_of_lt_of_le (by positivity : 0 < E / 16) hb
  let d := E / N
  let z := N / b
  have hd : 0 < d := div_pos hE hN
  have hdEta : d <= eta := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    have hCancel : d * N = E := by dsimp [d]; field_simp
    rw [hCancel]
    exact hSmall
  have hz : 1 <= z := by
    apply (mul_le_mul_iff_of_pos_right hbPos).mp
    have hCancel : z * b = N := by dsimp [z]; field_simp
    rw [hCancel]
    simpa only [one_mul] using hbN
  have hzUpper : z <= 16 / d := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    have hCancel : (16 / d) * d = 16 := by field_simp
    rw [hCancel]
    have hEq : z * d = E / b := by dsimp [z, d]; field_simp
    rw [hEq]
    apply (mul_le_mul_iff_of_pos_right hbPos).mp
    have hCancelB : (E / b) * b = E := by field_simp
    rw [hCancelB]
    linarith only [hb]
  have h := hAbs d z hd hdEta hz hzUpper
  have hScaled := mul_le_mul_of_nonneg_right h (by positivity : 0 <= X ^ 2 / ell ^ 4)
  dsimp [d, z, N] at hScaled
  convert hScaled using 1 <;> field_simp <;> ring

private theorem fullStep_prefix_defect_cover (S Z : Finset Nat) (M : Nat) :
    (SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card <=
      (SDiff.sdiff (inputPrimePrefix M) S).card + Z.card +
        (SDiff.sdiff (SDiff.sdiff (nextPrimeWindow M) Z) (fullStep S)).card := by
  classical
  let D := SDiff.sdiff (inputPrimePrefix M) S
  let B := SDiff.sdiff (SDiff.sdiff (nextPrimeWindow M) Z) (fullStep S)
  have hCover : SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S) <=
      Union.union (Union.union D Z) B := by
    intro r hr
    have h := Finset.mem_sdiff.mp hr
    rcases Finset.mem_union.mp (inputPrimePrefix_next_cover M h.1) with hOld | hNew
    next =>
      have hNotS : Not (Membership.mem S r) := fun hrS => h.2 (subset_fullStep S hrS)
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr (And.intro hOld hNotS)))
    next =>
      by_cases hz : Membership.mem Z r
      next => exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
      next => exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        (And.intro (Finset.mem_sdiff.mpr (And.intro hNew hz)) h.2))
  have h1 := Finset.card_le_card hCover
  have h2 := Finset.card_union_le (Union.union D Z) B
  have h3 := Finset.card_union_le D Z
  change (SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card <=
    D.card + Z.card + B.card
  omega

private theorem target_pos (M r : Nat) (hM : 3 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) : 0 < primeTargetSum r := by
  have h := nextPrimeWindow_spec M r hr
  unfold primeTargetSum
  split_ifs <;> omega

theorem exists_dense_fullStep_prefix_row_normalized_recurrence (a : Real) (ha : 0 < a) :
    exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S Z : Finset Nat,
        let P := inputPrimePrefix M
        let G := SDiff.sdiff (nextPrimeWindow M) Z
        let E := ((SDiff.sdiff P S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        (forall r, Membership.mem G r ->
          a * ((M : Real) / Real.log (M : Real) ^ 2) <=
            (1 / singularDivisorProduct (primeTargetSum r)) *
              ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + (Z.card : Real) +
            (8 * eta / a) * Real.log (M : Real))
        Filter.atTop) := by
  classical
  choose C hC hDelEvent using exists_averaged_fullStep_deletion_bound
  have hK : 0 < sieveThreeUpperConstant * C :=
    mul_pos sieveThreeUpperConstant_pos hC
  choose eta0 hEta0 hAbs0 using exists_dense_fraction_absorption a
    (sieveThreeUpperConstant * C) ha hK
  let eta := min eta0 (min (a / 64) (a ^ 2 / 64))
  have hEta : 0 < eta := lt_min hEta0 (lt_min (by positivity) (by positivity))
  have hEtaOld : eta <= eta0 := min_le_left _ _
  have hEtaA : 64 * eta <= a := by
    have h := (min_le_right eta0 (min (a / 64) (a ^ 2 / 64))).trans (min_le_left _ _)
    change eta <= a / 64 at h
    linarith only [h]
  have hEtaSq : 64 * eta <= a ^ 2 := by
    have h := (min_le_right eta0 (min (a / 64) (a ^ 2 / 64))).trans (min_le_right _ _)
    change eta <= a ^ 2 / 64 at h
    linarith only [h]
  have hAbs : forall d z : Real, 0 < d -> d <= eta -> 1 <= z -> z <= 16 / d ->
      8 * d * (sieveThreeUpperConstant * C) * Real.log (3 + Real.log z) <= a ^ 2 :=
    fun d z hd hdEta hz hzUpper => hAbs0 d z hd (hdEta.trans hEtaOld) hz hzUpper
  let D := 8 * eta / a
  have hD : 0 < D := div_pos (mul_pos (by norm_num) hEta) ha

  have hLarge : Filter.Eventually (fun M : Nat => 5 ^ 8 <= M) Filter.atTop :=
    Filter.eventually_ge_atTop _
  refine Exists.intro eta (And.intro hEta ?_)
  filter_upwards [hDelEvent, eventually_nextPrimeWindow_card_le_half, hLarge]
    with M hDel hWindow hM
  intro S Z
  let P := inputPrimePrefix M
  let G := SDiff.sdiff (nextPrimeWindow M) Z
  let B := SDiff.sdiff G (fullStep S)
  let E : Real := ((SDiff.sdiff P S).card : Real)
  let b : Real := (B.card : Real)
  let N : Real := (M : Real) / Real.log (M : Real)
  let F : Real := (M : Real) / Real.log (M : Real) ^ 4
  let L : Real := a * ((M : Real) / Real.log (M : Real) ^ 2)
  let U : Real := 1 / L
  let V0 : Real := sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3)
  let V : Real := V0 / L ^ 2
  let v0 := fun r => 1 / singularDivisorProduct (primeTargetSum r)
  let v := primeTargetRowNormalizer P
  change E <= eta * N ->
    (forall r, Membership.mem G r ->
      L <= v0 r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
    ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
      (17 / 16 : Real) * E + (Z.card : Real) + D * Real.log (M : Real)
  intro hE hRep
  have hM3 : 3 <= M := by
    have h := (Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM
    omega
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  have hLog := (sieveScaleCutoff_log_bounds M hM).1
  have hN : 0 < N := div_pos hMR hLog
  have hF : 0 < F := div_pos hMR (pow_pos hLog 4)
  have hL : 0 < L := mul_pos ha (div_pos hMR (pow_pos hLog 2))
  have hU : 0 <= U := by dsimp [U]; positivity
  have hV0 : 0 <= V0 := by
    have h := sieveThreeUpperConstant_pos
    dsimp [V0]
    positivity
  have hV : 0 <= V := div_nonneg hV0 (sq_nonneg L)
  have hENonneg : 0 <= E := Nat.cast_nonneg _
  have hBG : B <= G := fun r hr => (Finset.mem_sdiff.mp hr).1
  have hBR : B <= nextPrimeWindow M :=
    fun r hr => (Finset.mem_sdiff.mp (hBG hr)).1
  have hbR : b <= ((nextPrimeWindow M).card : Real) := by
    dsimp [b]
    exact_mod_cast Finset.card_le_card hBR
  change ((nextPrimeWindow M).card : Real) <= N / 2 at hWindow
  have hbN : b <= N := by linarith only [hbR, hWindow, hN]
  have hv : forall r, Membership.mem B r -> 0 <= v r := by
    intro r hr
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hMissing : forall r, Membership.mem B r ->
      Not (Membership.mem (fullStep S) r) :=
    fun r hr => (Finset.mem_sdiff.mp hr).2
  have hFullLower : forall r, Membership.mem B r ->
      L <= ((Finset.sumPartners P (primeTargetSum r)).card : Real) := by
    intro r hr
    have hOrig : v0 r <= 1 := by
      have h := one_div_le_one_div_of_le zero_lt_one
        (sieve_singularDivisorProduct_one_le (primeTargetSum r))
      simpa only [div_one] using h
    have hCard := mul_le_mul_of_nonneg_right hOrig
      (Nat.cast_nonneg (Finset.sumPartners P (primeTargetSum r)).card)
    exact (hRep r (hBG hr)).trans (by simpa only [one_mul] using hCard)
  have hNewRep : forall r, Membership.mem B r ->
      (1 : Real) <= v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real) := by
    intro r hr
    have hRp : 0 < ((Finset.sumPartners P (primeTargetSum r)).card : Real) :=
      hL.trans_le (hFullLower r hr)
    change (1 : Real) <=
      (1 / ((Finset.sumPartners P (primeTargetSum r)).card : Real)) *
        ((Finset.sumPartners P (primeTargetSum r)).card : Real)
    have hEq : (1 / ((Finset.sumPartners P (primeTargetSum r)).card : Real)) *
        ((Finset.sumPartners P (primeTargetSum r)).card : Real) = (1 : Real) := by
      field_simp [ne_of_gt hRp]
    rw [hEq]
  have hSelf : forall r, Membership.mem B r ->
      Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) <= U := by
    intro r hr
    exact primeTarget_normalized_self_upper P r L hL (hFullLower r hr)
  have hCross : forall r, Membership.mem B r -> forall s, Membership.mem B s ->
      Not (s = r) ->
      Finset.sum P (fun p => primeTargetWeight P v p r * primeTargetWeight P v p s) <=
        V * singularDivisorProduct (primeTargetSeparation r s) := by
    intro r hr s hs hne
    have hR := nextPrimeWindow_spec M r (hBR hr)
    have hS := nextPrimeWindow_spec M s (hBR hs)
    have hDifferent : Not (primeTargetSum r = primeTargetSum s) := by
      intro he
      exact hne (primeTarget_injective_window M r s hM3 hR.1 hS.1 hR.2 hS.2 he).symm
    have hOld := primeTargetWeight_cross_upper_sieve M hM r s
      (target_pos M r hM3 (hBR hr)) (target_pos M s hM3 (hBR hs)) hDifferent
    have hSep : 0 <= singularDivisorProduct (primeTargetSeparation r s) :=
      zero_le_one.trans (sieve_singularDivisorProduct_one_le _)
    have hNorm := primeTarget_normalized_cross_upper P v0 r s L
      (V0 * singularDivisorProduct (primeTargetSeparation r s)) hL
      (mul_nonneg hV0 hSep) (hRep r (hBG hr)) (hRep s (hBG hs)) hOld
    convert hNorm using 1 <;> dsimp [V] <;> ring
  have hDLog : 0 <= D * Real.log (M : Real) := mul_nonneg (le_of_lt hD) (le_of_lt hLog)
  have hBad : b <= E / 16 + D * Real.log (M : Real) := by
    by_cases hFloor : b < F
    next =>
      by_cases hEmpty : Not B.Nonempty
      next =>
        have hCardZero : B.card = 0 := by
          by_contra h
          have hPos : 0 < B.card := by omega
          exact hEmpty (Finset.card_pos.mp hPos)
        have hbZero : b = 0 := by dsimp [b]; rw [hCardZero]; norm_num
        linarith only [hbZero, hENonneg, hDLog]
      next =>
        choose r hr using not_not.mp hEmpty
        have hR := nextPrimeWindow_spec M r (hBR hr)
        have hr3 : 3 <= r := by omega
        have hBound := primeTarget_missing_normalized_degree_le_two P S r
          hR.1 hr3 (hMissing r hr)
        have hRepBound : a * ((M : Real) / Real.log (M : Real) ^ 2) <= 2 * E := by
          exact (hRep r (hBG hr)).trans hBound
        have hFloorE := small_target_floor_absorbed_under_density (M : Real)
          (Real.log (M : Real)) a eta E hMR hLog ha hEta.le hENonneg
          hEtaA hEtaSq hE hRepBound
        change F <= E / 16 at hFloorE
        linarith only [hFloor, hFloorE, hDLog]
    next =>
      have hSize : F <= b := le_of_not_gt hFloor
      by_cases hFew : b < E / 16
      next => linarith only [hFew, hDLog]
      next =>
        have hbE : E / 16 <= b := le_of_not_gt hFew
        have hSmall : 8 * E * (V * C * Real.log (3 + Real.log (N / b))) <= (1 : Real) ^ 2 := by
          by_cases hZero : E = 0
          next => simp only [hZero, mul_zero, zero_mul]; exact sq_nonneg (1 : Real)
          next =>
            have hEPos : 0 < E := lt_of_le_of_ne hENonneg (Ne.symm hZero)
            have h := absorption_scaled a (sieveThreeUpperConstant * C) eta hAbs
              (M : Real) (Real.log (M : Real)) E b hMR hLog hEPos hE hbE hbN
            have hOld : 8 * E * (V0 * C * Real.log (3 + Real.log (N / b))) <= L ^ 2 := by
              convert h using 1 <;> dsimp [V0, L, N] <;> ring
            apply (mul_le_mul_iff_of_pos_right (pow_pos hL 2)).mp
            have hCancel : (8 * E * (V * C * Real.log (3 + Real.log (N / b)))) * L ^ 2 =
                8 * E * (V0 * C * Real.log (3 + Real.log (N / b))) := by
              dsimp [V]
              field_simp [ne_of_gt hL] <;> ring
            rw [hCancel]
            simpa only [one_pow, one_mul] using hOld
        have hDeleted := hDel P S B v 1 U V hBR hSize (by norm_num) hU hV hv hMissing
          hNewRep hSelf hCross hSmall
        have hCoeff : 0 <= 8 * U := by positivity
        have hUpper : b <= D * Real.log (M : Real) := by
          calc
            b <= 8 * E * U / (1 : Real) ^ 2 := hDeleted
            _ = (8 * U) * E := by norm_num; ring
            _ <= (8 * U) * (eta * N) :=
              mul_le_mul_of_nonneg_left hE hCoeff
            _ = D * Real.log (M : Real) := by
              dsimp [D, U, L, N]
              field_simp
        linarith only [hUpper, hENonneg]
  have hPrefix : ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
      E + (Z.card : Real) + b := by
    dsimp [E, b, P, B, G]
    exact_mod_cast fullStep_prefix_defect_cover S Z M
  linarith only [hPrefix, hBad]

end PrimeFactorOscillations.LPF
