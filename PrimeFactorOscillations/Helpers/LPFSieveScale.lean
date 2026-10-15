/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSievePrimeForms

/-!
# Uniform input-scale upper sieve bounds

An integer maximal power cutoff applies to every input size. No restriction
to perfect powers and no unproved floor or logarithmic comparison is used.
-/

namespace PrimeFactorOscillations.LPF

def sieveScaleCutoff (M : Nat) : Nat :=
  Nat.findGreatest (fun z => z ^ 8 <= M) M

theorem sieveScaleCutoff_pow_le (M : Nat) : sieveScaleCutoff M ^ 8 <= M := by
  exact Nat.findGreatest_spec (P := fun z => z ^ 8 <= M) (m := 0)
    (Nat.zero_le M) (by simp)

theorem sieveScaleCutoff_next_pow_gt (M : Nat) :
    M < (sieveScaleCutoff M + 1) ^ 8 := by
  apply Nat.lt_of_not_ge
  intro h
  have hBound : sieveScaleCutoff M + 1 <= M :=
    (Nat.le_self_pow (by decide : Not (8 = 0)) _).trans h
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self (sieveScaleCutoff M)) hBound h

theorem sieveScaleCutoff_large (M : Nat) (hM : 5 ^ 8 <= M) :
    5 <= sieveScaleCutoff M :=
  Nat.le_findGreatest
    ((Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM) hM

private theorem half_le_log_two : (1 / 2 : Real) <= Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : Real) < Inv.inv 2 by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

theorem sieveScaleCutoff_log_bounds (M : Nat) (hM : 5 ^ 8 <= M) :
    And (0 < Real.log (M : Real))
      (And (1 <= Real.log (M : Real))
        (Real.log (M : Real) <= 16 * Real.log (sieveScaleCutoff M : Real))) := by
  let z := sieveScaleCutoff M
  have hz : 5 <= z := sieveScaleCutoff_large M hM
  have hzPos : (0 : Real) < (z : Real) := by exact_mod_cast (show 0 < z by omega)
  have hzM : z <= M := (Nat.le_self_pow (by decide : Not (8 = 0)) z).trans
    (sieveScaleCutoff_pow_le M)
  have hMPos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogM : 0 < Real.log (M : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLog4 : Real.log (4 : Real) = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hLog4M := Real.log_le_log (show (0 : Real) < 4 by norm_num)
    (show (4 : Real) <= (M : Real) by exact_mod_cast (show 4 <= M by omega))
  have hLarge : 1 <= Real.log (M : Real) := by
    rw [hLog4] at hLog4M
    linarith [half_le_log_two]
  have hMUpper : (M : Real) <= (2 * (z : Real)) ^ 8 := by
    have hNat := (le_of_lt (sieveScaleCutoff_next_pow_gt M)).trans
      (Nat.pow_le_pow_left (show z + 1 <= 2 * z by omega) 8)
    exact_mod_cast hNat
  have hLogUpper := Real.log_le_log hMPos hMUpper
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hzPos)] at hLogUpper
  have hLog2Z : Real.log 2 <= Real.log (z : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 <= z by omega))
  have hFinal : Real.log (M : Real) <= 16 * Real.log (z : Real) := by
    norm_num at hLogUpper
    linarith
  exact And.intro hLogM (And.intro hLarge hFinal)

private theorem power_compare {a b : Real} (ha : 0 <= a) (hab : a <= b) (k : Nat) :
    a ^ k <= b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) k)

private theorem log_five_le : Real.log 5 <= (9 / 5 : Real) := by
  have hp : (5 : Real) <= ((6 : Real) / 5) ^ 9 := by norm_num
  have hl := Real.log_le_log (show (0 : Real) < 5 by norm_num) hp
  rw [Real.log_pow] at hl
  have hr := Real.log_le_sub_one_of_pos (show (0 : Real) < (6 : Real) / 5 by norm_num)
  norm_num at hl hr
  linarith

private theorem log_linear_bound (z : Nat) (hz : 5 <= z) :
    Real.log (z : Real) <= (9 / 25 : Real) * (z : Real) := by
  have hzR : (5 : Real) <= (z : Real) := by exact_mod_cast hz
  have hzPos : (0 : Real) < (z : Real) := by linarith only [hzR]
  have h := Real.log_le_sub_one_of_pos (div_pos hzPos (by norm_num : (0 : Real) < 5))
  rw [Real.log_div (ne_of_gt hzPos) (by norm_num)] at h
  linarith [log_five_le]

theorem sieveScaleCutoff_exception_bounds (M : Nat) (hM : 5 ^ 8 <= M) :
    And (2 * (sieveScaleCutoff M : Real) <= (M : Real) / Real.log (M : Real) ^ 2)
      (3 * (sieveScaleCutoff M : Real) <= (M : Real) / Real.log (M : Real) ^ 3) := by
  let z := sieveScaleCutoff M
  have hz : 5 <= z := sieveScaleCutoff_large M hM
  have hzNN : (0 : Real) <= (z : Real) := Nat.cast_nonneg z
  have hLogs := sieveScaleCutoff_log_bounds M hM
  have hLogZ := log_linear_bound z hz
  have hLogUpper : Real.log (M : Real) <= (144 / 25 : Real) * (z : Real) := by
    linarith only [hLogs.2.2, hLogZ]
  have hCube := power_compare (le_of_lt hLogs.1) hLogUpper 3
  have hScaled := mul_le_mul_of_nonneg_left hCube
    (show 0 <= 3 * (z : Real) by positivity)
  have hCoef : (3 * (144 / 25) ^ 3 : Real) <= (z : Real) ^ 4 := by
    have hNat := Nat.pow_le_pow_left hz 4
    have hReal : (5 : Real) ^ 4 <= (z : Real) ^ 4 := by exact_mod_cast hNat
    norm_num at hReal
    linarith
  have hPoly : 3 * (z : Real) * ((144 / 25 : Real) * (z : Real)) ^ 3 <= (M : Real) := by
    calc
      _ = (3 * (144 / 25) ^ 3 : Real) * (z : Real) ^ 4 := by ring
      _ <= (z : Real) ^ 4 * (z : Real) ^ 4 :=
        mul_le_mul_of_nonneg_right hCoef (pow_nonneg hzNN 4)
      _ = (z : Real) ^ 8 := by rw [<- pow_add]
      _ <= _ := by exact_mod_cast sieveScaleCutoff_pow_le M
  have hSmall3 := hScaled.trans hPoly
  have hTwoToThree : 2 * (z : Real) * Real.log (M : Real) ^ 2 <=
      3 * (z : Real) * Real.log (M : Real) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right
      (show (2 : Real) <= 3 * Real.log (M : Real) by linarith only [hLogs.2.1])
      (mul_nonneg hzNN (sq_nonneg (Real.log (M : Real))))
    convert h using 1 <;> ring
  have hSmall2 := hTwoToThree.trans hSmall3
  have hne : Not (Real.log (M : Real) = 0) := ne_of_gt hLogs.1
  constructor
  next =>
    apply (mul_le_mul_iff_of_pos_right (pow_pos hLogs.1 2)).mp
    field_simp
    nlinarith only [hSmall2]
  next =>
    apply (mul_le_mul_iff_of_pos_right (pow_pos hLogs.1 3)).mp
    field_simp
    nlinarith only [hSmall3]

private theorem one_le_factor_product (P : Finset Nat)
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

theorem sieve_singularDivisorProduct_one_le (v : Nat) : 1 <= singularDivisorProduct v :=
  one_le_factor_product _ (fun p hp => (Finset.mem_filter.mp hp).2)

private theorem scaled_main_term_le (k : Nat) (A M c u v G : Real)
    (hA : 0 <= A) (hM : 0 <= M) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v)
    (hG : 0 <= G) (hAM : A <= 3 * M) (hUV : v <= 48 * u) :
    72 * A * G / (c ^ k * u ^ k) <=
      (216 * 48 ^ k / c ^ k) * (M / v ^ k) * G := by
  have hPow := power_compare (le_of_lt hv) hUV k
  rw [mul_pow] at hPow
  have hRaw := mul_le_mul hAM hPow (pow_nonneg (le_of_lt hv) k) (by positivity : 0 <= 3 * M)
  have hScaled := mul_le_mul_of_nonneg_left hRaw (mul_nonneg (by norm_num : (0 : Real) <= 72) hG)
  have hnc : Not (c = 0) := ne_of_gt hc
  have hnu : Not (u = 0) := ne_of_gt hu
  have hnv : Not (v = 0) := ne_of_gt hv
  apply (mul_le_mul_iff_of_pos_right
    (mul_pos (mul_pos (pow_pos hc k) (pow_pos hu k)) (pow_pos hv k))).mp
  field_simp
  nlinarith only [hScaled]

private theorem sharp_scaled_main_term_le (k : Nat) (A M c u v G : Real)
    (hA : 0 <= A) (hM : 0 <= M) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v)
    (hG : 0 <= G) (hAM : A <= 3 * M) (hUV : v <= 16 * u) :
    144 * A * G / (c ^ k * u ^ k) <=
      (432 * 16 ^ k / c ^ k) * (M / v ^ k) * G := by
  have hPow := power_compare (le_of_lt hv) hUV k
  rw [mul_pow] at hPow
  have hRaw := mul_le_mul hAM hPow (pow_nonneg (le_of_lt hv) k) (by positivity : 0 <= 3 * M)
  have hScaled := mul_le_mul_of_nonneg_left hRaw (mul_nonneg (by norm_num : (0 : Real) <= 144) hG)
  have hnc : Not (c = 0) := ne_of_gt hc
  have hnu : Not (u = 0) := ne_of_gt hu
  have hnv : Not (v = 0) := ne_of_gt hv
  apply (mul_le_mul_iff_of_pos_right
    (mul_pos (mul_pos (pow_pos hc k) (pow_pos hu k)) (pow_pos hv k))).mp
  field_simp
  nlinarith only [hScaled]

noncomputable def sieveTwoUpperConstant : Real :=
  216 * 48 ^ 2 / sieveMertensConstant ^ 2 + 1

noncomputable def sieveThreeUpperConstant : Real :=
  216 * 48 ^ 3 / sieveMertensConstant ^ 3 + 1

private theorem scale_auxiliary (M : Nat) (hM : 5 ^ 8 <= M) :
    And (1 < sieveScaleCutoff M ^ 4) ((sieveScaleCutoff M ^ 4) ^ 2 <= M) := by
  have hz := sieveScaleCutoff_large M hM
  have hQ := Nat.pow_le_pow_left (show 2 <= sieveScaleCutoff M by omega) 4
  norm_num at hQ
  refine And.intro (by omega) ?_
  simpa only [<- pow_mul] using sieveScaleCutoff_pow_le M

/-- A fixed explicit constant bounds actual two-prime representations at every large input size. -/
theorem prime_twoForm_scale_bound (M : Nat) (hM : 5 ^ 8 <= M)
    (t : Nat) (ht : 0 < t) (X : Finset Nat) (hX : X <= Finset.range (M + 1))
    (hPrime : forall k, Membership.mem X k -> And (Nat.Prime k) (Nat.Prime (t - k))) :
    (X.card : Real) <= sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) *
      singularDivisorProduct t := by
  let z := sieveScaleCutoff M
  let Q := z ^ 4
  have hz := sieveScaleCutoff_large M hM
  have hLogs := sieveScaleCutoff_log_bounds M hM
  have hAux := scale_auxiliary M hM
  have hBound := prime_twoForm_card_le z t (by omega) ht X
    (N := M + 1) (Q := Q) (by omega) hAux.1 hX hPrime (le_refl _)
  have hzPos : (0 : Real) < (z : Real) := by exact_mod_cast (show 0 < z by omega)
  have hLogZ : 0 < Real.log (z : Real) := Real.log_pos
    (by exact_mod_cast (show 1 < z by omega))
  have hLogComparison : Real.log (M : Real) <= 48 * Real.log (z : Real) := by
    linarith only [hLogs.2.2, hLogZ]
  have hMR : (0 : Real) <= (M : Real) := Nat.cast_nonneg M
  have hNum : ((M + 1 : Nat) : Real) + (Q : Real) ^ 2 <= 3 * (M : Real) := by
    have hQBound : (Q : Real) ^ 2 <= (M : Real) := by exact_mod_cast hAux.2
    have hM1 : 1 <= M := by have h := (Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM; omega
    have hM1R : (1 : Real) <= (M : Real) := by exact_mod_cast hM1
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hG := sieve_singularDivisorProduct_one_le t
  have hMain := scaled_main_term_le 2
    (((M + 1 : Nat) : Real) + (Q : Real) ^ 2) (M : Real) sieveMertensConstant
    (Real.log (z : Real)) (Real.log (M : Real)) (singularDivisorProduct t)
    (by positivity) hMR sieveMertensConstant_pos hLogZ hLogs.1
    (zero_le_one.trans hG) hNum hLogComparison
  have hSmall := (sieveScaleCutoff_exception_bounds M hM).1
  have hSmallG := mul_le_mul_of_nonneg_left hG
    (show 0 <= (M : Real) / Real.log (M : Real) ^ 2 by positivity)
  dsimp [sieveTwoUpperConstant]
  nlinarith only [hBound, hMain, hSmall, hSmallG]

/-- The full three-prime codegree scale is uniform in both positive distinct targets. -/
theorem prime_threeForm_scale_bound (M : Nat) (hM : 5 ^ 8 <= M)
    (t s : Nat) (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s))
    (X : Finset Nat) (hX : X <= Finset.range (M + 1))
    (hPrime : forall k, Membership.mem X k ->
      And (Nat.Prime k) (And (Nat.Prime (t - k)) (Nat.Prime (s - k)))) :
    (X.card : Real) <= sieveThreeUpperConstant * ((M : Real) / Real.log (M : Real) ^ 3) *
      (singularDivisorProduct t * singularDivisorProduct s *
        singularDivisorProduct ((t - s) + (s - t))) := by
  let z := sieveScaleCutoff M
  let Q := z ^ 4
  have hz := sieveScaleCutoff_large M hM
  have hLogs := sieveScaleCutoff_log_bounds M hM
  have hAux := scale_auxiliary M hM
  have hBound := prime_threeForm_card_le z t s (by omega) ht hs hne X
    (N := M + 1) (Q := Q) (by omega) hAux.1 hX hPrime (le_refl _)
  have hLogZ : 0 < Real.log (z : Real) := Real.log_pos
    (by exact_mod_cast (show 1 < z by omega))
  have hMR : (0 : Real) <= (M : Real) := Nat.cast_nonneg M
  have hNum : ((M + 1 : Nat) : Real) + (Q : Real) ^ 2 <= 3 * (M : Real) := by
    have hQBound : (Q : Real) ^ 2 <= (M : Real) := by exact_mod_cast hAux.2
    have hM1 : 1 <= M := by have h := (Nat.le_self_pow (by decide : Not (8 = 0)) 5).trans hM; omega
    have hM1R : (1 : Real) <= (M : Real) := by exact_mod_cast hM1
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  let G := singularDivisorProduct t * singularDivisorProduct s *
    singularDivisorProduct ((t - s) + (s - t))
  have htG := sieve_singularDivisorProduct_one_le t
  have hsG := sieve_singularDivisorProduct_one_le s
  have hdG := sieve_singularDivisorProduct_one_le ((t - s) + (s - t))
  have hPair : 1 <= singularDivisorProduct t * singularDivisorProduct s := by
    simpa using mul_le_mul htG hsG zero_le_one (zero_le_one.trans htG)
  have hG : 1 <= G := by
    simpa [G] using mul_le_mul hPair hdG zero_le_one (zero_le_one.trans hPair)
  have hMain := sharp_scaled_main_term_le 3
    (((M + 1 : Nat) : Real) + (Q : Real) ^ 2) (M : Real) sieveMertensConstant
    (Real.log (z : Real)) (Real.log (M : Real)) G
    (by positivity) hMR sieveMertensConstant_pos hLogZ hLogs.1
    (zero_le_one.trans hG) hNum hLogs.2.2
  have hSmall := (sieveScaleCutoff_exception_bounds M hM).2
  have hSmallG := mul_le_mul_of_nonneg_left hG
    (show 0 <= (M : Real) / Real.log (M : Real) ^ 3 by positivity)
  have hCoefficient : (432 * 16 ^ 3 : Real) / sieveMertensConstant ^ 3 <=
      (216 * 48 ^ 3 : Real) / sieveMertensConstant ^ 3 :=
    div_le_div_of_nonneg_right (by norm_num)
      (pow_nonneg sieveMertensConstant_pos.le 3)
  have hCoefficientScaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCoefficient
      (show 0 <= (M : Real) / Real.log (M : Real) ^ 3 by positivity))
    (zero_le_one.trans hG)
  have hMainOld := hMain.trans hCoefficientScaled
  dsimp [sieveThreeUpperConstant]
  nlinarith only [hBound, hMainOld, hSmall, hSmallG]

theorem sieveTwoUpperConstant_pos : 0 < sieveTwoUpperConstant := by
  have h := sieveMertensConstant_pos
  dsimp [sieveTwoUpperConstant]
  positivity

theorem sieveThreeUpperConstant_pos : 0 < sieveThreeUpperConstant := by
  have h := sieveMertensConstant_pos
  dsimp [sieveThreeUpperConstant]
  positivity

/-- The two-form constant is chosen before the input size, target, and counted set. -/
theorem exists_uniform_twoForm_upper_bound :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat => forall t : Nat, 0 < t ->
        forall X : Finset Nat, X <= Finset.range (M + 1) ->
          (forall k, Membership.mem X k -> And (Nat.Prime k) (Nat.Prime (t - k))) ->
        (X.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 2) *
          singularDivisorProduct t) Filter.atTop) := by
  refine Exists.intro sieveTwoUpperConstant (And.intro sieveTwoUpperConstant_pos ?_)
  apply Filter.eventually_atTop.mpr
  exact Exists.intro (5 ^ 8) (fun M hM t ht X hX hPrime =>
    prime_twoForm_scale_bound M hM t ht X hX hPrime)

/-- One three-form constant is uniform in both positive distinct targets and counted sets. -/
theorem exists_uniform_threeForm_upper_bound :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat => forall t s : Nat,
        0 < t -> 0 < s -> Not (t = s) ->
        forall X : Finset Nat, X <= Finset.range (M + 1) ->
          (forall k, Membership.mem X k ->
            And (Nat.Prime k) (And (Nat.Prime (t - k)) (Nat.Prime (s - k)))) ->
        (X.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 3) *
          (singularDivisorProduct t * singularDivisorProduct s *
            singularDivisorProduct ((t - s) + (s - t)))) Filter.atTop) := by
  refine Exists.intro sieveThreeUpperConstant (And.intro sieveThreeUpperConstant_pos ?_)
  apply Filter.eventually_atTop.mpr
  exact Exists.intro (5 ^ 8) (fun M hM t s ht hs hne X hX hPrime =>
    prime_threeForm_scale_bound M hM t s ht hs hne X hX hPrime)

end PrimeFactorOscillations.LPF
