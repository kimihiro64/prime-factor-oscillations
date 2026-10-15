/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFUpperSieve

/-!
# Dense-seed generation recurrence

The complete normalized overlap absorption and growth comparison are
proved before consuming the actual prime-target deletion bound.
-/

set_option autoImplicit false

namespace PrimeFactorOscillations.LPF

private theorem exists_sum_of_card_sumPartners_gt (P S : Finset Nat) (n : Nat)
    (hCount : 2 * (SDiff.sdiff P S).card < (Finset.sumPartners P n).card) :
    exists p, exists q, And (Membership.mem S p) (And (Membership.mem S q) (p + q = n)) := by
  classical
  by_contra h
  let D := SDiff.sdiff P S
  have hCover : Finset.sumPartners P n <= Union.union D (D.image (fun p => n - p)) := by
    intro p hp
    have hP := Finset.mem_filter.mp hp
    by_cases hpS : Membership.mem S p
    next =>
      have hqS : Not (Membership.mem S (n - p)) := by
        intro hq
        exact h (Exists.intro p (Exists.intro (n - p) (And.intro hpS (And.intro hq (by omega)))))
      have hqD : Membership.mem D (n - p) := Finset.mem_sdiff.mpr (And.intro hP.2.1 hqS)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr (Exists.intro (n - p) (And.intro hqD (by omega)))
    next => exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr (And.intro hP.1 hpS))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le D (D.image (fun p => n - p))
  have hImage := Finset.card_image_le (s := D) (f := fun p => n - p)
  change 2 * D.card < (Finset.sumPartners P n).card at hCount
  omega

theorem primeTarget_missing_card_le_two (P S : Finset Nat) (r : Nat)
    (hr : Nat.Prime r) (hr3 : 3 <= r) (hMissing : Not (Membership.mem (fullStep S) r)) :
    (Finset.sumPartners P (primeTargetSum r)).card <= 2 * (SDiff.sdiff P S).card := by
  by_contra hToo
  have hCount : 2 * (SDiff.sdiff P S).card < (Finset.sumPartners P (primeTargetSum r)).card := by omega
  choose p q hp hq hSum using exists_sum_of_card_sumPartners_gt P S (primeTargetSum r) hCount
  have hFull := mem_fullStep_of_pair S hp hq
  have hLift := primeTarget_lift r hr hr3
  have hOwner := primeTarget_owner r hr hr3
  have hAffine : affineValue p q = primeTargetCofactor r * r := by
    unfold affineValue
    rw [hSum]
    omega
  rw [hAffine, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hOwner.1) hr hOwner.2] at hFull
  exact hMissing hFull

private theorem small_target_factor_product_one (P : Finset Nat)
    (hP : forall p, Membership.mem P p -> 3 <= p) :
    1 <= Finset.prod P singularFactor := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp]
    have hThree : (3 : Real) <= (p : Real) := by exact_mod_cast hP p (Finset.mem_insert_self p P)
    have hDen : 0 < (p : Real) - 2 := by linarith
    have hRec : 0 <= 1 / ((p : Real) - 2) := by positivity
    have hFactor : 1 <= singularFactor p := by dsimp [singularFactor]; linarith
    have hTail := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
    simpa using mul_le_mul hFactor hTail zero_le_one (zero_le_one.trans hFactor)

theorem primeTarget_missing_normalized_degree_le_two (P S : Finset Nat) (r : Nat)
    (hr : Nat.Prime r) (hr3 : 3 <= r) (hMissing : Not (Membership.mem (fullStep S) r)) :
    (1 / singularDivisorProduct (primeTargetSum r)) *
      ((Finset.sumPartners P (primeTargetSum r)).card : Real) <=
        2 * ((SDiff.sdiff P S).card : Real) := by
  have hCard : ((Finset.sumPartners P (primeTargetSum r)).card : Real) <=
      2 * ((SDiff.sdiff P S).card : Real) := by
    exact_mod_cast primeTarget_missing_card_le_two P S r hr hr3 hMissing
  have hG : 1 <= singularDivisorProduct (primeTargetSum r) :=
    small_target_factor_product_one _ (fun p hp => (Finset.mem_filter.mp hp).2)
  have hGPos : 0 < singularDivisorProduct (primeTargetSum r) := by linarith only [hG]
  have hv : 1 / singularDivisorProduct (primeTargetSum r) <= (1 : Real) := by
    apply (mul_le_mul_iff_of_pos_right hGPos).mp
    have hCancel : (1 / singularDivisorProduct (primeTargetSum r)) *
        singularDivisorProduct (primeTargetSum r) = (1 : Real) := by field_simp
    rw [hCancel, one_mul]
    exact hG
  exact (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _)).trans (by simpa only [one_mul] using hCard)

theorem small_target_floor_absorbed (X ell a E : Real) (ha : 0 < a)
    (hell : 0 < ell) (hE : 0 <= E)
    (hRep : a * (X / ell ^ 2) <= 2 * E) (hScale : 32 <= a * ell ^ 2) :
    X / ell ^ 4 <= E / 16 := by
  have hScaled := mul_le_mul_of_nonneg_right hRep (sq_nonneg ell)
  have hCancel : (a * (X / ell ^ 2)) * ell ^ 2 = a * X := by field_simp
  rw [hCancel] at hScaled
  have hCondition := mul_le_mul_of_nonneg_right hScale (by positivity : 0 <= E * ell ^ 2)
  apply (mul_le_mul_iff_of_pos_right (pow_pos hell 4)).mp
  have hCancelX : (X / ell ^ 4) * ell ^ 4 = X := by field_simp
  rw [hCancelX]
  apply (mul_le_mul_iff_of_pos_left ha).mp
  nlinarith only [hScaled, hCondition]

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

private theorem eventually_log_mul_lt_floor (D : Real) :
    Filter.Eventually (fun M : Nat =>
      D * Real.log (M : Real) < (M : Real) / Real.log (M : Real) ^ 4)
      Filter.atTop := by
  choose R hR using exists_nat_gt (max 0 D * 16 ^ 5)
  let K := max 5 R
  apply Filter.eventually_atTop.mpr
  refine Exists.intro (K ^ 8) ?_
  intro M hM
  have hK : 5 <= K := le_max_left _ _
  have hRK : R <= K := le_max_right _ _
  have hLarge : 5 ^ 8 <= M :=
    (Nat.pow_le_pow_left hK 8).trans hM
  let z := sieveScaleCutoff M
  have hKM : K <= M := (Nat.le_self_pow (by decide : Not (8 = 0)) K).trans hM
  have hKZ : K <= z := Nat.le_findGreatest hKM hM
  have hz : 5 <= z := hK.trans hKZ
  have hzPos : (0 : Real) < (z : Real) := by exact_mod_cast (by omega : 0 < z)
  have hLog := (sieveScaleCutoff_log_bounds M hLarge).1
  have hUpper := (sieveScaleCutoff_log_bounds M hLarge).2.2
  have hLogZ := Real.log_le_sub_one_of_pos hzPos
  have hA : Real.log (M : Real) <= 16 * (z : Real) := by linarith
  have hB : 0 <= 16 * (z : Real) := by positivity
  have hPow2 : Real.log (M : Real) ^ 2 <= (16 * (z : Real)) ^ 2 := by
    have h := mul_le_mul hA hA (le_of_lt hLog) hB
    simpa only [pow_two] using h
  have hPow4 : Real.log (M : Real) ^ 4 <= (16 * (z : Real)) ^ 4 := by
    have h := mul_le_mul hPow2 hPow2 (sq_nonneg _) (sq_nonneg _)
    convert h using 1 <;> ring
  have hPow5 : Real.log (M : Real) ^ 5 <= (16 * (z : Real)) ^ 5 := by
    have h := mul_le_mul hPow4 hA (le_of_lt hLog) (by positivity)
    convert h using 1 <;> ring
  have hDZ : max 0 D * (16 : Real) ^ 5 < (z : Real) := by
    have hCast : (R : Real) <= (z : Real) := by exact_mod_cast hRK.trans hKZ
    exact hR.trans_le hCast
  have hZ6 : (z : Real) ^ 6 <= (M : Real) := by
    have h := (Nat.pow_le_pow_right (by omega : 0 < z) (by omega : 6 <= 8)).trans
      (sieveScaleCutoff_pow_le M)
    exact_mod_cast h
  have hDPow : D * Real.log (M : Real) ^ 5 < (M : Real) := by
    have hD : D <= max 0 D := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_right hD (by positivity : 0 <= Real.log (M : Real) ^ 5)
    have h2 := mul_le_mul_of_nonneg_left hPow5 (le_max_left 0 D)
    have h3 := mul_lt_mul_of_pos_right hDZ (pow_pos hzPos 5)
    nlinarith only [h1, h2, h3, hZ6]
  apply (mul_lt_mul_iff_of_pos_right (pow_pos hLog 4)).mp
  have hCancel : ((M : Real) / Real.log (M : Real) ^ 4) * Real.log (M : Real) ^ 4 =
      (M : Real) := by field_simp
  rw [hCancel]
  convert hDPow using 1 <;> ring

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

/-- With a positive representation input, a fixed small prime defect contracts
relative to the growing prefix. Both upper sieve inputs and absorption are proved. -/
theorem exists_dense_fullStep_prefix_log_recurrence (a : Real) (ha : 0 < a) :
    exists eta D : Real, And (0 < eta) (And (0 < D)
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
            D * Real.log (M : Real))
        Filter.atTop)) := by
  classical
  choose C hC hDelEvent using exists_averaged_fullStep_deletion_bound
  have hK : 0 < sieveThreeUpperConstant * C :=
    mul_pos sieveThreeUpperConstant_pos hC
  choose eta hEta hAbs using exists_dense_fraction_absorption a
    (sieveThreeUpperConstant * C) ha hK
  let D := 8 * sieveTwoUpperConstant * eta / a ^ 2
  have hD : 0 < D := by
    dsimp [D]
    exact div_pos (mul_pos (mul_pos (by norm_num) sieveTwoUpperConstant_pos) hEta) (pow_pos ha 2)
  choose R hR using exists_nat_gt (Real.exp (max 1 (Real.sqrt (32 / a))))
  have hLogEvent : Filter.Eventually (fun M : Nat =>
      32 <= a * Real.log (M : Real) ^ 2) Filter.atTop := by
    filter_upwards [Filter.eventually_ge_atTop R] with M hM
    have hRM : (R : Real) <= (M : Real) := by exact_mod_cast hM
    have hExp : Real.exp (max 1 (Real.sqrt (32 / a))) <= (M : Real) :=
      le_of_lt (hR.trans_le hRM)
    have hLower : max 1 (Real.sqrt (32 / a)) <= Real.log (M : Real) := by
      have h := Real.log_le_log (Real.exp_pos _) hExp
      simpa only [Real.log_exp] using h
    have hOne : 1 <= Real.log (M : Real) := (le_max_left _ _).trans hLower
    have hRoot : Real.sqrt (32 / a) <= Real.log (M : Real) :=
      (le_max_right _ _).trans hLower
    have hSquare : 32 / a <= Real.log (M : Real) ^ 2 := by
      have h := mul_le_mul hRoot hRoot (Real.sqrt_nonneg _)
        (by linarith only [hOne] : 0 <= Real.log (M : Real))
      simpa only [<- pow_two, Real.sq_sqrt (by positivity : 0 <= 32 / a)] using h
    have h := mul_le_mul_of_nonneg_left hSquare (le_of_lt ha)
    have hCancel : a * (32 / a) = (32 : Real) := by field_simp
    rwa [hCancel] at h
  have hLarge : Filter.Eventually (fun M : Nat => 5 ^ 8 <= M) Filter.atTop :=
    Filter.eventually_ge_atTop _
  refine Exists.intro eta (Exists.intro D (And.intro hEta (And.intro hD ?_)))
  filter_upwards [hDelEvent, hLogEvent, eventually_nextPrimeWindow_card_le_half, hLarge]
    with M hDel hScale hWindow hM
  intro S Z
  let P := inputPrimePrefix M
  let G := SDiff.sdiff (nextPrimeWindow M) Z
  let B := SDiff.sdiff G (fullStep S)
  let E : Real := ((SDiff.sdiff P S).card : Real)
  let b : Real := (B.card : Real)
  let N : Real := (M : Real) / Real.log (M : Real)
  let F : Real := (M : Real) / Real.log (M : Real) ^ 4
  let L : Real := a * ((M : Real) / Real.log (M : Real) ^ 2)
  let U : Real := sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)
  let V : Real := sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3)
  let v := fun r => 1 / singularDivisorProduct (primeTargetSum r)
  change E <= eta * N ->
    (forall r, Membership.mem G r ->
      L <= v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
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
  have hU : 0 <= U := by
    have h := sieveTwoUpperConstant_pos
    dsimp [U]
    positivity
  have hV : 0 <= V := by
    have h := sieveThreeUpperConstant_pos
    dsimp [V]
    positivity
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
    exact div_nonneg zero_le_one
      (zero_le_one.trans (sieve_singularDivisorProduct_one_le _))
  have hMissing : forall r, Membership.mem B r ->
      Not (Membership.mem (fullStep S) r) :=
    fun r hr => (Finset.mem_sdiff.mp hr).2
  have hSelf : forall r, Membership.mem B r ->
      Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) <= U := by
    intro r hr
    exact primeTargetWeight_self_upper_sieve M hM r (target_pos M r hM3 (hBR hr))
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
    exact primeTargetWeight_cross_upper_sieve M hM r s
      (target_pos M r hM3 (hBR hr)) (target_pos M s hM3 (hBR hs)) hDifferent
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
        have hFloorE := small_target_floor_absorbed (M : Real)
          (Real.log (M : Real)) a E ha hLog hENonneg hRepBound hScale
        change F <= E / 16 at hFloorE
        linarith only [hFloor, hFloorE, hDLog]
    next =>
      have hSize : F <= b := le_of_not_gt hFloor
      by_cases hFew : b < E / 16
      next => linarith only [hFew, hDLog]
      next =>
        have hbE : E / 16 <= b := le_of_not_gt hFew
        have hSmall : 8 * E * (V * C * Real.log (3 + Real.log (N / b))) <= L ^ 2 := by
          by_cases hZero : E = 0
          next => simp only [hZero, mul_zero, zero_mul]; exact sq_nonneg L
          next =>
            have hEPos : 0 < E := lt_of_le_of_ne hENonneg (Ne.symm hZero)
            have h := absorption_scaled a (sieveThreeUpperConstant * C) eta hAbs
              (M : Real) (Real.log (M : Real)) E b hMR hLog hEPos hE hbE hbN
            convert h using 1 <;> dsimp [V, L, N] <;> ring
        have hDeleted := hDel P S B v L U V hBR hSize hL hU hV hv hMissing
          (fun r hr => hRep r (hBG hr)) hSelf hCross hSmall
        have hCoeff : 0 <= 8 * U / L ^ 2 := by positivity
        have hUpper : b <= D * Real.log (M : Real) := by
          calc
            b <= 8 * E * U / L ^ 2 := hDeleted
            _ = (8 * U / L ^ 2) * E := by ring
            _ <= (8 * U / L ^ 2) * (eta * N) :=
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

/-- The earlier floor-error interface follows from the stronger logarithmic
remainder. This preserves downstream consumers while retaining the sharper bound. -/
theorem exists_dense_fullStep_prefix_recurrence (a : Real) (ha : 0 < a) :
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
            (M : Real) / Real.log (M : Real) ^ 4)
        Filter.atTop) := by
  choose eta D hEta hD hEvent using exists_dense_fullStep_prefix_log_recurrence a ha
  refine Exists.intro eta (And.intro hEta ?_)
  filter_upwards [hEvent, eventually_log_mul_lt_floor D] with M hRec hFloor
  intro S Z
  dsimp only
  intro hE hRep
  have h := hRec S Z hE hRep
  linarith only [h, hFloor]

end PrimeFactorOscillations.LPF
