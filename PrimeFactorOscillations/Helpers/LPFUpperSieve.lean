/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedTransfer
import PrimeFactorOscillations.Helpers.LPFSieveScale

/-!
# Proved upper sieve inputs for the actual generation weights

The normalized self and cross bounds are derived from the maintained
upper sieve for two and three prime forms, including small forms and diagonals.
-/

namespace PrimeFactorOscillations.LPF

private theorem partner_subset_range (M t : Nat) :
    Finset.sumPartners (inputPrimePrefix M) t <= Finset.range (M + 1) := by
  intro p hp
  have hP := Finset.mem_filter.mp hp
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hP.1).1
  exact Finset.mem_range.mpr (by omega)

private theorem partner_prime_forms (M t p : Nat)
    (hp : Membership.mem (Finset.sumPartners (inputPrimePrefix M) t) p) :
    And (Nat.Prime p) (Nat.Prime (t - p)) := by
  have hP := Finset.mem_filter.mp hp
  exact And.intro (Finset.mem_filter.mp hP.1).2 (Finset.mem_filter.mp hP.2.1).2

private theorem partner_card_bound (M : Nat) (hM : 5 ^ 8 <= M)
    (t : Nat) (ht : 0 < t) :
    ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) <=
      sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) *
        singularDivisorProduct t :=
  prime_twoForm_scale_bound M hM t ht _ (partner_subset_range M t)
    (fun p hp => partner_prime_forms M t p hp)

private theorem partner_cross_card_bound (M : Nat) (hM : 5 ^ 8 <= M)
    (t s : Nat) (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s)) :
    ((Inter.inter (Finset.sumPartners (inputPrimePrefix M) t)
      (Finset.sumPartners (inputPrimePrefix M) s)).card : Real) <=
      sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3) *
        (singularDivisorProduct t * singularDivisorProduct s *
          singularDivisorProduct ((t - s) + (s - t))) := by
  apply prime_threeForm_scale_bound M hM t s ht hs hne
  next =>
    intro p hp
    exact partner_subset_range M t (Finset.mem_inter.mp hp).1
  next =>
    intro p hp
    have h := Finset.mem_inter.mp hp
    have hT := partner_prime_forms M t p h.1
    have hS := partner_prime_forms M s p h.2
    exact And.intro hT.1 (And.intro hT.2 hS.2)

private theorem sum_weight_sq (P : Finset Nat) (v : Nat -> Real) (r : Nat) :
    Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) =
      (v r) ^ 2 * ((Finset.sumPartners P (primeTargetSum r)).card : Real) := by
  classical
  let A := Finset.sumPartners P (primeTargetSum r)
  have hPoint : forall p, primeTargetWeight P v p r ^ 2 =
      if Membership.mem A p then (v r) ^ 2 else 0 := by
    intro p
    by_cases hp : Membership.mem A p <;> simp [primeTargetWeight, A, hp]
  have hSet : P.filter (fun p => Membership.mem A p) = A := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    next => intro h; exact h.2
    next => intro h; exact And.intro (Finset.mem_filter.mp h).1 h
  calc
    _ = Finset.sum P (fun p => if Membership.mem A p then (v r) ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hPoint p
    _ = Finset.sum (P.filter (fun p => Membership.mem A p)) (fun _ => (v r) ^ 2) := by
      rw [Finset.sum_filter]
    _ = _ := by rw [hSet]; simp <;> ring

private theorem sum_weight_cross (P : Finset Nat) (v : Nat -> Real) (r s : Nat) :
    Finset.sum P (fun p => primeTargetWeight P v p r * primeTargetWeight P v p s) =
      (v r * v s) * ((Inter.inter (Finset.sumPartners P (primeTargetSum r))
        (Finset.sumPartners P (primeTargetSum s))).card : Real) := by
  classical
  let A := Finset.sumPartners P (primeTargetSum r)
  let B := Finset.sumPartners P (primeTargetSum s)
  have hPoint : forall p, primeTargetWeight P v p r * primeTargetWeight P v p s =
      if And (Membership.mem A p) (Membership.mem B p) then v r * v s else 0 := by
    intro p
    by_cases hr : Membership.mem A p <;> by_cases hs : Membership.mem B p <;>
      simp [primeTargetWeight, A, B, hr, hs]
  have hSet : P.filter (fun p => And (Membership.mem A p) (Membership.mem B p)) =
      Inter.inter A B := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    next => intro h; exact h.2
    next => intro h; exact And.intro (Finset.mem_filter.mp h.1).1 h
  calc
    _ = Finset.sum P (fun p =>
        if And (Membership.mem A p) (Membership.mem B p) then v r * v s else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hPoint p
    _ = Finset.sum (P.filter (fun p => And (Membership.mem A p) (Membership.mem B p)))
        (fun _ => v r * v s) := by rw [Finset.sum_filter]
    _ = _ := by rw [hSet]; simp <;> ring

private theorem normalize_self (a K G : Real) (hG : 1 <= G) (hK : 0 <= K)
    (hA : a <= K * G) : (1 / G) ^ 2 * a <= K := by
  have hGPos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hne : Not (G = 0) := ne_of_gt hGPos
  have hScaled := mul_le_mul_of_nonneg_left hA (sq_nonneg (1 / G))
  have hCancel : (1 / G) ^ 2 * (K * G) = K / G := by field_simp <;> ring
  have hKG := mul_le_mul_of_nonneg_left hG hK
  calc
    _ <= (1 / G) ^ 2 * (K * G) := hScaled
    _ = K / G := hCancel
    _ <= K := by
      apply (mul_le_mul_iff_of_pos_right hGPos).mp
      field_simp
      nlinarith only [hKG]

private theorem normalize_cross (a K G H D : Real) (hG : 0 < G) (hH : 0 < H)
    (hA : a <= K * (G * H * D)) :
    (1 / G * (1 / H)) * a <= K * D := by
  have hnG : Not (G = 0) := ne_of_gt hG
  have hnH : Not (H = 0) := ne_of_gt hH
  calc
    _ <= (1 / G * (1 / H)) * (K * (G * H * D)) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by field_simp <;> ring

/-- The actual normalized self-energy input is proved, including input diagonals. -/
theorem primeTargetWeight_self_upper_sieve (M : Nat) (hM : 5 ^ 8 <= M)
    (r : Nat) (hr : 0 < primeTargetSum r) :
    Finset.sum (inputPrimePrefix M) (fun p =>
      primeTargetWeight (inputPrimePrefix M)
        (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p r ^ 2) <=
      sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) := by
  rw [sum_weight_sq]
  have hK : 0 <= sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) := by
    have h := sieveTwoUpperConstant_pos
    positivity
  exact normalize_self _ _ _ (sieve_singularDivisorProduct_one_le _) hK
    (partner_card_bound M hM (primeTargetSum r) hr)

/-- The actual normalized cross energy retains only the target-separation factor. -/
theorem primeTargetWeight_cross_upper_sieve (M : Nat) (hM : 5 ^ 8 <= M)
    (r s : Nat) (hr : 0 < primeTargetSum r) (hs : 0 < primeTargetSum s)
    (hne : Not (primeTargetSum r = primeTargetSum s)) :
    Finset.sum (inputPrimePrefix M) (fun p =>
      primeTargetWeight (inputPrimePrefix M)
        (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p r *
      primeTargetWeight (inputPrimePrefix M)
        (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p s) <=
      sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3) *
        singularDivisorProduct (primeTargetSeparation r s) := by
  rw [sum_weight_cross]
  exact normalize_cross _ _ _ _ _
    (lt_of_lt_of_le zero_lt_one (sieve_singularDivisorProduct_one_le _))
    (lt_of_lt_of_le zero_lt_one (sieve_singularDivisorProduct_one_le _))
    (partner_cross_card_bound M hM (primeTargetSum r) (primeTargetSum s) hr hs hne)

private theorem target_sum_pos (M r : Nat) (hM : 3 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) : 0 < primeTargetSum r := by
  have h := nextPrimeWindow_spec M r hr
  unfold primeTargetSum
  split_ifs <;> omega

/-- Both upper inputs hold uniformly for every prime target in the actual next window. -/
theorem exists_primeTarget_upper_sieve_inputs :
    exists U0 V0 : Real, And (0 < U0) (And (0 < V0)
      (Filter.Eventually (fun M : Nat =>
        And
          (forall r, Membership.mem (nextPrimeWindow M) r ->
            Finset.sum (inputPrimePrefix M) (fun p =>
              primeTargetWeight (inputPrimePrefix M)
                (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p r ^ 2) <=
              U0 * ((M : Real) / Real.log (M : Real) ^ 2))
          (forall r, Membership.mem (nextPrimeWindow M) r ->
            forall s, Membership.mem (nextPrimeWindow M) s -> Not (s = r) ->
            Finset.sum (inputPrimePrefix M) (fun p =>
              primeTargetWeight (inputPrimePrefix M)
                (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p r *
              primeTargetWeight (inputPrimePrefix M)
                (fun r => 1 / singularDivisorProduct (primeTargetSum r)) p s) <=
              V0 * ((M : Real) / Real.log (M : Real) ^ 3) *
                singularDivisorProduct (primeTargetSeparation r s)) ) Filter.atTop)) := by
  refine Exists.intro sieveTwoUpperConstant (Exists.intro sieveThreeUpperConstant
    (And.intro sieveTwoUpperConstant_pos (And.intro sieveThreeUpperConstant_pos ?_)))
  apply Filter.eventually_atTop.mpr
  refine Exists.intro (5 ^ 8) ?_
  intro M hM
  have hM3 : 3 <= M := by
    have h := (Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM
    omega
  constructor
  next =>
    intro r hr
    exact primeTargetWeight_self_upper_sieve M hM r (target_sum_pos M r hM3 hr)
  next =>
    intro r hr s hs hne
    have hR := nextPrimeWindow_spec M r hr
    have hS := nextPrimeWindow_spec M s hs
    have hDifferent : Not (primeTargetSum r = primeTargetSum s) := by
      intro he
      exact hne (primeTarget_injective_window M r s hM3 hR.1 hS.1 hR.2 hS.2 he).symm
    exact primeTargetWeight_cross_upper_sieve M hM r s
      (target_sum_pos M r hM3 hr) (target_sum_pos M s hM3 hs) hDifferent

/-- Actual upper inputs are discharged; only positive supply and absorption remain explicit. -/
theorem exists_sieved_fullStep_prefix_bound :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat =>
        forall (S Z : Finset Nat) (L : Real),
        let P := inputPrimePrefix M
        let G := SDiff.sdiff (nextPrimeWindow M) Z
        let B := SDiff.sdiff G (fullStep S)
        let E := ((SDiff.sdiff P S).card : Real)
        let F := (M : Real) / Real.log (M : Real) ^ 4
        let U := sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)
        let V := sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3)
        0 < L ->
        (forall r, Membership.mem G r ->
          L <= (1 / singularDivisorProduct (primeTargetSum r)) *
            ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
        (F <= (B.card : Real) -> 8 * E *
          (V * C * Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real))))
          <= L ^ 2) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          E + (Z.card : Real) + F + 8 * E * U / L ^ 2)
        Filter.atTop) := by
  choose C hC hOld using exists_averaged_fullStep_prefix_bound
  refine Exists.intro C (And.intro hC ?_)
  have hLarge : Filter.Eventually (fun M : Nat => 5 ^ 8 <= M) Filter.atTop :=
    Filter.eventually_atTop.mpr (Exists.intro (5 ^ 8) (fun _ h => h))
  apply (hOld.and hLarge).mono
  intro M hBoth S Z L
  have hBase := hBoth.1
  have hM := hBoth.2
  dsimp only
  intro hL hRep hSmall
  let P := inputPrimePrefix M
  let G := SDiff.sdiff (nextPrimeWindow M) Z
  let v := fun r => 1 / singularDivisorProduct (primeTargetSum r)
  let U := sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)
  let V := sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3)
  have hM3 : 3 <= M := by
    have h := (Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM
    omega
  have hLog := (sieveScaleCutoff_log_bounds M hM).1
  have hU : 0 <= U := by
    have h := sieveTwoUpperConstant_pos
    dsimp [U]
    positivity
  have hV : 0 <= V := by
    have h := sieveThreeUpperConstant_pos
    dsimp [V]
    positivity
  have hv : forall r, Membership.mem G r -> 0 <= v r := by
    intro r hr
    exact div_nonneg zero_le_one (zero_le_one.trans (sieve_singularDivisorProduct_one_le _))
  have hSelf : forall r, Membership.mem G r ->
      Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) <= U := by
    intro r hr
    have hR := (Finset.mem_sdiff.mp hr).1
    exact primeTargetWeight_self_upper_sieve M hM r (target_sum_pos M r hM3 hR)
  have hCross : forall r, Membership.mem G r -> forall s, Membership.mem G s ->
      Not (s = r) ->
      Finset.sum P (fun p => primeTargetWeight P v p r * primeTargetWeight P v p s) <=
        V * singularDivisorProduct (primeTargetSeparation r s) := by
    intro r hr s hs hne
    have hrR := (Finset.mem_sdiff.mp hr).1
    have hsR := (Finset.mem_sdiff.mp hs).1
    have hR := nextPrimeWindow_spec M r hrR
    have hS := nextPrimeWindow_spec M s hsR
    have hDifferent : Not (primeTargetSum r = primeTargetSum s) := by
      intro he
      exact hne (primeTarget_injective_window M r s hM3 hR.1 hS.1 hR.2 hS.2 he).symm
    exact primeTargetWeight_cross_upper_sieve M hM r s
      (target_sum_pos M r hM3 hrR) (target_sum_pos M s hM3 hsR) hDifferent
  exact hBase S Z v L U V hL hU hV hv hRep hSelf hCross hSmall

private theorem sq_loglog_le (x : Real) (hx : 0 < x) (hx1 : x <= 1) :
    x ^ 2 * Real.log (3 + Real.log (16 / x ^ 2)) <= 20 * x := by
  have hx0 : Not (x = 0) := ne_of_gt hx
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hxSq1 : x ^ 2 <= 1 := by nlinarith
  have hRatio : (1 : Real) <= 16 / x ^ 2 := by
    have hCancel : (16 / x ^ 2) * x ^ 2 = 16 := by field_simp
    apply (mul_le_mul_iff_of_pos_right hxSq).mp
    rw [hCancel]
    nlinarith
  have hInner : 0 <= Real.log (16 / x ^ 2) := Real.log_nonneg hRatio
  have hArg : 0 < 3 + Real.log (16 / x ^ 2) := by linarith
  have hOuter := Real.log_le_sub_one_of_pos hArg
  have hInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hInv
  have hLog : Real.log (16 / x ^ 2) = Real.log 16 - 2 * Real.log x := by
    rw [Real.log_div (by norm_num : Not ((16 : Real) = 0)) (pow_ne_zero 2 hx0),
      Real.log_pow]
    norm_num
  have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 16)
  have hOuterMul := mul_le_mul_of_nonneg_left hOuter (sq_nonneg x)
  have hInvMul := mul_le_mul_of_nonneg_left hInv (sq_nonneg x)
  have h16Mul := mul_le_mul_of_nonneg_left h16 (sq_nonneg x)
  have hCancel : x ^ 2 * (Inv.inv x - 1) = x - x ^ 2 := by
    field_simp
  have hInvMul' : -(x ^ 2 * Real.log x) <= x - x ^ 2 := by
    nlinarith only [hInvMul, hCancel]
  have hSquare : x ^ 2 <= x := by nlinarith
  rw [hLog] at hOuterMul
  rw [hLog]
  nlinarith only [hOuterMul, hInvMul', h16Mul, hSquare, hx]

/-- An explicit admissible fraction for the complete overlap allowance. -/
theorem dense_fraction_absorption_explicit (a K : Real) (ha : 0 < a) (hK : 0 < K) :
    forall d z : Real,
      0 < d -> d <= (min 1 (a ^ 2 / (160 * K))) ^ 2 -> 1 <= z -> z <= 16 / d ->
      8 * d * K * Real.log (3 + Real.log z) <= a ^ 2 := by
  let t := min 1 (a ^ 2 / (160 * K))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t <= 1 := min_le_left _ _
  have htA : t <= a ^ 2 / (160 * K) := min_le_right _ _
  intro d z hd hdSmall hz hRatio
  let x := Real.sqrt d
  have hx : 0 < x := Real.sqrt_pos.mpr hd
  have hxSq : x ^ 2 = d := Real.sq_sqrt (le_of_lt hd)
  have hxt : x <= t := by nlinarith only [hdSmall, hxSq, hx, ht]
  have hx1 : x <= 1 := hxt.trans ht1
  have hLogZ : Real.log z <= Real.log (16 / d) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hz) hRatio
  have hArg : 0 < 3 + Real.log z := by
    have h := Real.log_nonneg hz
    linarith
  have hLogLog : Real.log (3 + Real.log z) <= Real.log (3 + Real.log (16 / d)) :=
    Real.log_le_log hArg (by linarith)
  have hBound := sq_loglog_le x hx hx1
  rw [hxSq] at hBound
  have hScaled := mul_le_mul_of_nonneg_left hLogLog (by positivity : 0 <= d)
  have hScaled2 := mul_le_mul_of_nonneg_left hBound (by positivity : 0 <= 8 * K)
  have hRatioBound : 160 * K * x <= a ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (hxt.trans htA)
      (by positivity : 0 <= 160 * K)
    have hCancel : (160 * K) * (a ^ 2 / (160 * K)) = a ^ 2 := by field_simp
    rw [hCancel] at h
    exact h
  have hScaled3 := mul_le_mul_of_nonneg_left hScaled (by positivity : 0 <= 8 * K)
  nlinarith only [hScaled3, hScaled2, hRatioBound]

/-- A fixed small fraction absorbs the complete logarithmic overlap term. -/
theorem exists_dense_fraction_absorption (a K : Real) (ha : 0 < a) (hK : 0 < K) :
    exists eta : Real, And (0 < eta) (forall d z : Real,
      0 < d -> d <= eta -> 1 <= z -> z <= 16 / d ->
      8 * d * K * Real.log (3 + Real.log z) <= a ^ 2) := by
  refine Exists.intro ((min 1 (a ^ 2 / (160 * K))) ^ 2) (And.intro ?_ ?_)
  next => exact sq_pos_of_pos (lt_min (by norm_num) (by positivity))
  next => exact dense_fraction_absorption_explicit a K ha hK

end PrimeFactorOscillations.LPF
