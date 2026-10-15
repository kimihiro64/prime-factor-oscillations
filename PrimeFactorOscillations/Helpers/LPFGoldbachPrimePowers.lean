/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDenseDensity
import PrimeFactorOscillations.Helpers.LPFPrimePowerMass
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.WeightedPrimePower

/-!
# Prime-power removal for bounded Goldbach inputs

The full two-position Mangoldt loss is bounded uniformly and converted to
precisely the normalized prime-pair supply used by the LPF transfer.
The positive weighted source and its exceptional set are not proved here.
-/

set_option autoImplicit false

namespace PrimeFactorOscillations.LPF

noncomputable def goldbachMangoldtWeight (A : Finset Nat) (t : Nat) : Real :=
  Finset.sum A (fun p => ArithmeticFunction.vonMangoldt p * ArithmeticFunction.vonMangoldt (t - p))

private noncomputable def primeLogWeight (n : Nat) : Real := if Nat.Prime n then Real.log (n : Real) else 0

noncomputable def goldbachPrimeLogWeight (A : Finset Nat) (t : Nat) : Real :=
  Finset.sum A (fun p => primeLogWeight p * primeLogWeight (t - p))

private theorem primeLogWeight_nonneg (n : Nat) : 0 <= primeLogWeight n := by
  by_cases hp : Nat.Prime n
  next =>
    have h : 0 < Real.log (n : Real) := Real.log_pos (by exact_mod_cast hp.one_lt)
    simpa [primeLogWeight, hp] using h.le
  next => simp [primeLogWeight, hp]

private theorem primeLogWeight_le_mangoldt (n : Nat) :
    primeLogWeight n <= ArithmeticFunction.vonMangoldt n := by
  by_cases hp : Nat.Prime n
  next => simp [primeLogWeight, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  next => simp [primeLogWeight, hp, ArithmeticFunction.vonMangoldt_nonneg]

/-- The exact two-position loss consumes the complete prime-power mass bound. -/
theorem goldbach_primePower_difference_bound_of_mass (A : Finset Nat) (M t : Nat) (hM : 1 <= M)
    (B : Real) (hPsi : Chebyshev.psi (M : Real) - Chebyshev.theta (M : Real) <= B)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p)) :
    And (0 <= goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t)
      (goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t <=
        2 * B * Real.log (M : Real)) := by
  classical
  let d := fun n => ArithmeticFunction.vonMangoldt n - primeLogWeight n
  let ell := Real.log (M : Real)
  have hd (n : Nat) : 0 <= d n := sub_nonneg.mpr (primeLogWeight_le_mangoldt n)
  have hEll : 0 <= ell := Real.log_nonneg (by exact_mod_cast hM)
  have hLambda (n : Nat) (hn : Membership.mem (Finset.Icc 1 M) n) :
      ArithmeticFunction.vonMangoldt n <= ell := by
    have hnSpec := Finset.mem_Icc.mp hn
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnSpec.2))
  have hPrimeLog (n : Nat) (hn : Membership.mem (Finset.Icc 1 M) n) :
      primeLogWeight n <= ell := (primeLogWeight_le_mangoldt n).trans (hLambda n hn)
  have hMass : Finset.sum (Finset.Icc 1 M) d =
      Chebyshev.psi (M : Real) - Chebyshev.theta (M : Real) := by
    unfold Chebyshev.psi Chebyshev.theta
    simp only [Nat.floor_natCast, Finset.sum_filter]
    have hset : Finset.Icc 1 M = Finset.Ioc 0 M := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    simp only [d, primeLogWeight, Finset.sum_sub_distrib]
  have hMassBound : Finset.sum (Finset.Icc 1 M) d <=
      B := by
    rw [hMass]
    exact hPsi
  have hP : Finset.sum A d <= B :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => hInput p hp) (fun n _ _ => hd n)).trans hMassBound
  have hQImage : forall q, Membership.mem (A.image (fun p => t - p)) q ->
      Membership.mem (Finset.Icc 1 M) q := by
    intro q hq
    choose p hp hEq using Finset.mem_image.mp hq
    rw [<- hEq]
    exact hPartner p hp
  have hInj : Set.InjOn (fun p => t - p) (A : Set Nat) := by
    intro p hp q hq hEq
    have hpPos := Finset.mem_Icc.mp (hPartner p hp)
    have hqPos := Finset.mem_Icc.mp (hPartner q hq)
    change t - p = t - q at hEq
    omega
  have hQ : Finset.sum A (fun p => d (t - p)) <=
      B := by
    rw [<- Finset.sum_image hInj]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => hQImage q hq) (fun n _ _ => hd n)).trans hMassBound
  have hId : goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t =
      Finset.sum A (fun p => d p * ArithmeticFunction.vonMangoldt (t - p)) +
      Finset.sum A (fun p => primeLogWeight p * d (t - p)) := by
    rw [<- Finset.sum_add_distrib]
    unfold goldbachMangoldtWeight goldbachPrimeLogWeight
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [d]
    ring
  rw [hId]
  refine And.intro ?_ ?_
  next =>
    exact add_nonneg
      (Finset.sum_nonneg (fun p _ => mul_nonneg (hd p) ArithmeticFunction.vonMangoldt_nonneg))
      (Finset.sum_nonneg (fun p _ => mul_nonneg (primeLogWeight_nonneg p) (hd (t - p))))
  next =>
    have hFirst : Finset.sum A (fun p => d p * ArithmeticFunction.vonMangoldt (t - p)) <=
        (Finset.sum A d) * ell := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hLambda (t - p) (hPartner p hp)) (hd p)
    have hSecond : Finset.sum A (fun p => primeLogWeight p * d (t - p)) <=
        ell * Finset.sum A (fun p => d (t - p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (hPrimeLog p (hInput p hp)) (hd (t - p))
    have hFirstBound := hFirst.trans (mul_le_mul_of_nonneg_right hP hEll)
    have hSecondBound := hSecond.trans (mul_le_mul_of_nonneg_left hQ hEll)
    dsimp [ell] at hFirstBound hSecondBound
    nlinarith only [hFirstBound, hSecondBound]

/-- The original square-root-log mass bound remains available unchanged. -/
theorem goldbach_primePower_difference_bound (A : Finset Nat) (M t : Nat) (hM : 1 <= M)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p)) :
    And (0 <= goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t)
      (goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t <=
        4 * Real.sqrt (M : Real) * Real.log (M : Real) ^ 2) := by
  have h := goldbach_primePower_difference_bound_of_mass A M t hM
    (2 * Real.sqrt (M : Real) * Real.log (M : Real))
    (Chebyshev.psi_sub_theta_le (by exact_mod_cast hM)) hInput hPartner
  refine And.intro h.1 ?_
  convert h.2 using 1 <;> ring

/-- The full two-position loss retains only one logarithm above the explicit
square-root mass cutoff. -/
theorem goldbach_primePower_difference_linear_bound (A : Finset Nat) (M t : Nat)
    (hM : 2 ^ 20 <= M)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p)) :
    And (0 <= goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t)
      (goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t <=
        4 * Real.sqrt (M : Real) * Real.log (M : Real)) := by
  have hMass := primePower_mass_sqrt_explicit (M : Real) (by exact_mod_cast hM)
  have h := goldbach_primePower_difference_bound_of_mass A M t (by omega)
    (2 * Real.sqrt (M : Real)) hMass hInput hPartner
  refine And.intro h.1 ?_
  convert h.2 using 1 <;> ring

theorem goldbachPrimeLogWeight_le_card (A : Finset Nat) (M t : Nat) (hM : 1 <= M)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p)) :
    goldbachPrimeLogWeight A t <=
      ((A.filter (fun p => And (Nat.Prime p) (Nat.Prime (t - p)))).card : Real) *
        Real.log (M : Real) ^ 2 := by
  classical
  let B := A.filter (fun p => And (Nat.Prime p) (Nat.Prime (t - p)))
  have hId : goldbachPrimeLogWeight A t =
      Finset.sum B (fun p => Real.log (p : Real) * Real.log ((t - p : Nat) : Real)) := by
    dsimp [goldbachPrimeLogWeight, B]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpPrime : Nat.Prime p <;> by_cases hqPrime : Nat.Prime (t - p) <;>
      simp [primeLogWeight, hpPrime, hqPrime]
  rw [hId]
  calc
    _ <= Finset.sum B (fun _ => Real.log (M : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hB := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Icc.mp (hInput p hB.1)
      have hqI := Finset.mem_Icc.mp (hPartner p hB.1)
      have hpLog : Real.log (p : Real) <= Real.log (M : Real) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpI.2)
      have hqLog : Real.log ((t - p : Nat) : Real) <= Real.log (M : Real) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < t - p)) (by exact_mod_cast hqI.2)
      have hqNonneg : 0 <= Real.log ((t - p : Nat) : Real) := Real.log_nonneg (by exact_mod_cast hqI.1)
      have hMLog : 0 <= Real.log (M : Real) := Real.log_nonneg (by exact_mod_cast hM)
      simpa only [pow_two] using mul_le_mul hpLog hqLog hqNonneg hMLog
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]

/-- The actual source coefficient needs prime-power removal only above this
explicit cutoff, rather than a coarse eighth-power threshold. -/
theorem goldbach_primePower_loss_explicit (M : Nat) (hM : 2 ^ 44 <= M) :
    4 * Real.sqrt (M : Real) * Real.log (M : Real) ^ 2 <=
      (1 / 1024 : Real) * (M : Real) := by
  let v := Real.sqrt (Real.sqrt (M : Real))
  have hMPos : (0 : Real) < (M : Real) := by
    exact_mod_cast (by omega : 0 < M)
  have hSPos : 0 < Real.sqrt (M : Real) := Real.sqrt_pos.mpr hMPos
  have hvPos : 0 < v := Real.sqrt_pos.mpr hSPos
  have hv2 : v ^ 2 = Real.sqrt (M : Real) := Real.sq_sqrt hSPos.le
  have hv4 : v ^ 4 = (M : Real) := by
    calc
      _ = (v ^ 2) ^ 2 := by ring
      _ = _ := by rw [hv2, Real.sq_sqrt hMPos.le]
  have hBase : (2048 : Real) ^ 4 <= v ^ 4 := by
    rw [hv4]
    exact_mod_cast hM
  have hv : (2048 : Real) <= v := by
    rw [hv4] at hBase
    have hRoot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hBase)
    have hFirst : Real.sqrt ((2048 : Real) ^ 4) = (2048 : Real) ^ 2 := by
      rw [show (2048 : Real) ^ 4 = ((2048 : Real) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by norm_num)]
    rw [hFirst, Real.sqrt_sq (by norm_num)] at hRoot
    exact hRoot
  let u := v / 2048
  have hu : 1 <= u := by dsimp [u]; linarith only [hv]
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hLogU := Real.log_le_sub_one_of_pos huPos
  have hV : v = u * 2 ^ 11 := by dsimp [u]; norm_num
  have hLogM : Real.log (M : Real) = 4 * Real.log u + 44 * Real.log 2 := by
    rw [<- hv4, Real.log_pow, hV, Real.log_mul (ne_of_gt huPos) (by norm_num), Real.log_pow]
    ring
  have hBound : Real.log (M : Real) <= (220 / 7 : Real) * u := by
    have hTwo := log_two_le_five_sevenths
    rw [hLogM]
    nlinarith only [hLogU, hTwo, hu]
  have hLogNonneg : 0 <= Real.log (M : Real) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 <= M))
  have hSq : Real.log (M : Real) ^ 2 <= ((220 / 7 : Real) * u) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hBound hBound hLogNonneg (by positivity)
  have hCoef : 4 * Real.log (M : Real) ^ 2 <= (1 / 1024 : Real) * Real.sqrt (M : Real) := by
    rw [<- hv2]
    dsimp [u] at hSq
    nlinarith only [hSq]
  have h := mul_le_mul_of_nonneg_left hCoef (Real.sqrt_nonneg (M : Real))
  nlinarith only [h, Real.sq_sqrt hMPos.le]

/-- The explicit finite prime-power loss is negligible compared with M. -/
theorem eventually_goldbach_primePower_loss_small (a : Real) (ha : 0 < a) :
    Filter.Eventually (fun M : Nat =>
      4 * Real.sqrt (M : Real) * Real.log (M : Real) ^ 2 <= (a / 2) * (M : Real))
      Filter.atTop := by
  choose R hR using exists_nat_gt (max 5 (2048 / a))
  have hR5 : 5 <= R := by
    have h := (le_max_left (5 : Real) (2048 / a)).trans (le_of_lt hR)
    exact_mod_cast h
  have hRConst : 2048 / a < (R : Real) := (le_max_right _ _).trans_lt hR
  apply Filter.eventually_atTop.mpr
  refine Exists.intro (R ^ 8) ?_
  intro M hM
  let z := sieveScaleCutoff M
  have hzR : R <= z := Nat.le_findGreatest
    ((Nat.le_self_pow (by decide : Not (8 = 0)) R).trans hM) hM
  have hz5 : 5 <= z := hR5.trans hzR
  have hz1 : (1 : Real) <= (z : Real) := by exact_mod_cast (by omega : 1 <= z)
  have hzPos : (0 : Real) < (z : Real) := by linarith
  have hM5 : 5 ^ 8 <= M := (Nat.pow_le_pow_left hR5 8).trans hM
  have hLog := sieveScaleCutoff_log_bounds M hM5
  have hLogZ := Real.log_le_sub_one_of_pos hzPos
  have hLogUpper : Real.log (M : Real) <= 16 * (z : Real) := by
    have hLogComparison : Real.log (M : Real) <= 16 * Real.log (z : Real) := hLog.2.2
    linarith only [hLogComparison, hLogZ]
  have hLogSq : Real.log (M : Real) ^ 2 <= (16 * (z : Real)) ^ 2 := by
    have h := mul_le_mul hLogUpper hLogUpper hLog.1.le (by positivity)
    simpa only [pow_two] using h
  have hConst : (2048 : Real) < a * (z : Real) := by
    have hRz : (R : Real) <= (z : Real) := by exact_mod_cast hzR
    have h := mul_lt_mul_of_pos_left (hRConst.trans_le hRz) ha
    have hCancel : a * (2048 / a) = 2048 := by field_simp
    rw [hCancel] at h
    exact h
  have hPow34 : (z : Real) ^ 3 <= (z : Real) ^ 4 := by
    calc
      _ = (z : Real) ^ 3 * 1 := by ring
      _ <= (z : Real) ^ 3 * (z : Real) :=
        mul_le_mul_of_nonneg_left hz1 (by positivity)
      _ = _ := by ring
  have hSqrtSq : Real.sqrt (M : Real) ^ 2 = (M : Real) := Real.sq_sqrt (by positivity)
  have hCutSq : ((z : Real) ^ 4) ^ 2 <= (M : Real) := by
    rw [<- pow_mul]
    exact_mod_cast sieveScaleCutoff_pow_le M
  have hCutSqrt : (z : Real) ^ 4 <= Real.sqrt (M : Real) := by
    nlinarith only [hCutSq, hSqrtSq, Real.sqrt_nonneg (M : Real), pow_nonneg hzPos.le 4]
  have hCoef : 4 * Real.log (M : Real) ^ 2 <= (a / 2) * Real.sqrt (M : Real) := by
    calc
      _ <= 4 * (16 * (z : Real)) ^ 2 := mul_le_mul_of_nonneg_left hLogSq (by norm_num)
      _ = 1024 * (z : Real) ^ 2 := by ring
      _ <= (a / 2) * (z : Real) ^ 3 := by
        have h := mul_le_mul_of_nonneg_right hConst.le (sq_nonneg (z : Real))
        nlinarith only [h]
      _ <= (a / 2) * (z : Real) ^ 4 :=
        mul_le_mul_of_nonneg_left hPow34 (by positivity)
      _ <= _ := mul_le_mul_of_nonneg_left hCutSqrt (by positivity)
  have h := mul_le_mul_of_nonneg_left hCoef (Real.sqrt_nonneg (M : Real))
  calc
    _ = Real.sqrt (M : Real) * (4 * Real.log (M : Real) ^ 2) := by ring
    _ <= Real.sqrt (M : Real) * ((a / 2) * Real.sqrt (M : Real)) := h
    _ = (a / 2) * Real.sqrt (M : Real) ^ 2 := by ring
    _ = _ := by rw [hSqrtSq]

/-- Pointwise conversion retaining the entire signed prime-power deficit. -/
theorem goldbachMangoldt_to_sumPartners_of_deficit (a b : Real) (hb : 0 <= b)
    (M : Nat) (hM : 2 <= M) (A : Finset Nat) (t : Nat)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p))
    (hLoss : goldbachMangoldtWeight A t - goldbachPrimeLogWeight A t <= b * (M : Real))
    (hSupply : a * (M : Real) * singularDivisorProduct t <= goldbachMangoldtWeight A t) :
    (a - b) * ((M : Real) / Real.log (M : Real) ^ 2) <=
      (1 / singularDivisorProduct t) *
        ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) := by
  classical
  let B := A.filter (fun p => And (Nat.Prime p) (Nat.Prime (t - p)))
  have hSubset : B <= Finset.sumPartners (inputPrimePrefix M) t := by
    intro p hp
    have hB := Finset.mem_filter.mp hp
    have hpP : Membership.mem (inputPrimePrefix M) p :=
      Finset.mem_filter.mpr (And.intro (hInput p hB.1) hB.2.1)
    have hqP : Membership.mem (inputPrimePrefix M) (t - p) :=
      Finset.mem_filter.mpr (And.intro (hPartner p hB.1) hB.2.2)
    have hqPos := (Finset.mem_Icc.mp (hPartner p hB.1)).1
    exact Finset.mem_filter.mpr (And.intro hpP (And.intro hqP (by omega)))
  have hCard : (B.card : Real) <=
      ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) := by
    exact_mod_cast Finset.card_le_card hSubset
  have hPrimeLog := goldbachPrimeLogWeight_le_card A M t (by omega) hInput hPartner
  have hCardLog := mul_le_mul_of_nonneg_right hCard (sq_nonneg (Real.log (M : Real)))
  have hUpper : goldbachPrimeLogWeight A t <=
      ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) * Real.log (M : Real) ^ 2 :=
    hPrimeLog.trans hCardLog
  have hGone : 1 <= singularDivisorProduct t := sieve_singularDivisorProduct_one_le t
  have hG : 0 < singularDivisorProduct t := by linarith
  have hScaledLoss : b * (M : Real) <=
      b * (M : Real) * singularDivisorProduct t := by
    have h := mul_le_mul_of_nonneg_left hGone (by positivity : 0 <= b * (M : Real))
    simpa only [mul_one] using h
  have hMain : (a - b) * (M : Real) * singularDivisorProduct t <=
      ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) * Real.log (M : Real) ^ 2 := by
    nlinarith only [hSupply, hLoss, hScaledLoss, hUpper]
  have hLog : 0 < Real.log (M : Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  apply (mul_le_mul_iff_of_pos_right (mul_pos hG (pow_pos hLog 2))).mp
  have hLeft : ((a - b) * ((M : Real) / Real.log (M : Real) ^ 2)) *
      (singularDivisorProduct t * Real.log (M : Real) ^ 2) =
      (a - b) * (M : Real) * singularDivisorProduct t := by
    field_simp
  have hRight : ((1 / singularDivisorProduct t) *
      ((Finset.sumPartners (inputPrimePrefix M) t).card : Real)) *
      (singularDivisorProduct t * Real.log (M : Real) ^ 2) =
      ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) * Real.log (M : Real) ^ 2 := by
    field_simp
  rw [hLeft, hRight]
  exact hMain


/-- The half-loss interface specializes the exact signed deficit conversion. -/
theorem goldbachMangoldt_to_sumPartners_of_loss (a : Real) (ha : 0 < a)
    (M : Nat) (hM : 2 <= M)
    (hSmall : 4 * Real.sqrt (M : Real) * Real.log (M : Real) ^ 2 <=
      (a / 2) * (M : Real))
    (A : Finset Nat) (t : Nat)
    (hInput : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p)
    (hPartner : forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p))
    (hSupply : a * (M : Real) * singularDivisorProduct t <= goldbachMangoldtWeight A t) :
    (a / 2) * ((M : Real) / Real.log (M : Real) ^ 2) <=
      (1 / singularDivisorProduct t) *
        ((Finset.sumPartners (inputPrimePrefix M) t).card : Real) := by
  have hLoss := (goldbach_primePower_difference_bound A M t (by omega) hInput hPartner).2
  have h := goldbachMangoldt_to_sumPartners_of_deficit a (a / 2) (by positivity)
    M hM A t hInput hPartner (hLoss.trans hSmall) hSupply
  convert h using 1 <;> ring

/-- A bounded-input Mangoldt supply gives exactly the normalized prime-pair
input needed by the maintained LPF deletion and iteration theorems. -/
theorem eventually_goldbachMangoldt_to_sumPartners (a : Real) (ha : 0 < a) :
    Filter.Eventually (fun M : Nat =>
      forall A : Finset Nat, forall t : Nat,
      (forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) p) ->
      (forall p, Membership.mem A p -> Membership.mem (Finset.Icc 1 M) (t - p)) ->
      a * (M : Real) * singularDivisorProduct t <= goldbachMangoldtWeight A t ->
      (a / 2) * ((M : Real) / Real.log (M : Real) ^ 2) <=
        (1 / singularDivisorProduct t) *
          ((Finset.sumPartners (inputPrimePrefix M) t).card : Real)) Filter.atTop := by
  filter_upwards [eventually_goldbach_primePower_loss_small a ha,
    Filter.eventually_ge_atTop (2 : Nat)] with M hSmall hM
  intro A t hInput hPartner hSupply
  exact goldbachMangoldt_to_sumPartners_of_loss a ha M hM hSmall A t hInput hPartner hSupply

end PrimeFactorOscillations.LPF
