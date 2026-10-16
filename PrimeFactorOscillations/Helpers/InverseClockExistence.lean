/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FunProp
import PrimeFactorOscillations.Helpers.InverseClockDetector

/-!
# Inverse Clock Existence

Existence, localization and uniqueness of reference-clock inverses, proved by endpoint signs and the intermediate value theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.InverseClockDetector

theorem comparison_endpoint_margin (r N u K a T : Real)
    (hr : 0 < r) (hN : 0 < N) (hu : 0 < u) (ha : 0 < a)
    (hK : 0 <= K) (hrK : 2 * K <= r)
    (hLower : a <= r / u) (hT : 2 * K < a ^ 2 * T) :
    K * ((T / N) / u ^ 2 + 1 / (r * N)) <
      r / u ^ 2 * (T / N) := by
  have hTpos : 0 < T := by nlinarith [sq_pos_of_pos ha]
  have hb0 := mul_le_mul_of_nonneg_right hLower hu.le
  have hband : a * u <= r := by
    convert hb0 using 1 <;> field_simp [hu.ne']
  have hsq : a ^ 2 * u ^ 2 <= r ^ 2 := by
    nlinarith [mul_nonneg ha.le hu.le]
  have h1 := mul_le_mul_of_nonneg_right hsq hTpos.le
  have h2 := mul_lt_mul_of_pos_right hT (sq_pos_of_pos hu)
  have h3 := mul_le_mul_of_nonneg_right hrK (mul_nonneg hr.le hTpos.le)
  have hstrict : K * (r * T + u ^ 2) < r ^ 2 * T := by
    nlinarith only [h1, h2, h3]
  apply (mul_lt_mul_iff_of_pos_right
    (mul_pos (sq_pos_of_pos hu) (mul_pos hr hN))).mp
  convert hstrict using 1 <;> field_simp [hr.ne', hN.ne', hu.ne'] <;> ring

end PrimeFactorOscillations.InverseClockDetector
namespace PrimeFactorOscillations.PrimeClockLaw

theorem referenceRatio_continuousAt (law : PrimeClockLaw) (r : Nat) (u : Real)
    (hpos : 0 < Nat.factorialConvolution law.realCoefficient r u) :
    ContinuousAt (law.referenceRatio r) u := by
  have hc (k : Nat) : Continuous (Nat.factorialConvolution law.realCoefficient k) := by
    unfold Nat.factorialConvolution
    fun_prop
  exact (hc (r - 1)).continuousAt.div (hc r).continuousAt hpos.ne'

theorem exists_reference_inverse (law : PrimeClockLaw)
    (a : Real) (ha : 0 < a) (b : Real) (hb : 0 < b) :
    exists r0 N0 : Nat, exists C : Real,
      0 < r0 /\ 1 <= N0 /\ 0 < C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      3 <= law.arithmeticClock N ->
      a <= (r : Real) / (law.arithmeticClock N + 1) ->
      (r : Real) / (law.arithmeticClock N - 1) <= b ->
      exists U : Real,
        abs (U - law.arithmeticClock N) < C / (N : Real) /\
        abs (U - law.arithmeticClock N) <= 1 /\
        law.densityRatio N r = law.referenceRatio r U /\
        forall V : Real, abs (V - law.arithmeticClock N) <= 1 ->
          law.densityRatio N r = law.referenceRatio r V -> V = U := by
  choose rC NC K hrC hNC hK hCompare using law.exists_densityRatio_linearization b hb
  choose rS KS hrS hKS hSlope using law.exists_profile_reference_slope_bound b hb.le
  choose R hR using exists_nat_gt (2 * K + 2 * KS)
  let T := (2 * K + 1) / a ^ 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hTmargin : 2 * K < a ^ 2 * T := by
    have ht : a ^ 2 * T = 2 * K + 1 := by dsimp [T]; field_simp
    rw [ht]
    linarith
  choose NT hNT using exists_nat_gt T
  let r0 := max rC (max rS R)
  let N0 := max NC NT
  refine Exists.intro r0 (Exists.intro N0 (Exists.intro T
    (And.intro (hrC.trans_le (le_max_left _ _))
      (And.intro (hNC.trans (le_max_left _ _)) (And.intro hT ?_)))))
  intro r hr N hN hB hLower hUpper
  have hrC' : rC <= r := (le_max_left _ _).trans hr
  have hrS' : rS <= r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hRr : R <= r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hNC' : NC <= N := (le_max_left _ _).trans hN
  have hNT' : NT <= N := (le_max_right _ _).trans hN
  have hrPos : (0 : Real) < r := by exact_mod_cast (hrC.trans_le hrC')
  have hNPos : (0 : Real) < N := by exact_mod_cast (Nat.zero_lt_one.trans_le (hNC.trans hNC'))
  have hrK : 2 * K <= (r : Real) :=
    (by linarith : 2 * K <= (R : Real)).trans (by exact_mod_cast hRr)
  have hrKS : 2 * KS <= (r : Real) :=
    (by linarith : 2 * KS <= (R : Real)).trans (by exact_mod_cast hRr)
  have hTN : T < (N : Real) := hNT.trans_le (by exact_mod_cast hNT')
  let B := law.arithmeticClock N
  let h := T / (N : Real)
  let l := B - h
  let v := B + h
  have hh : 0 < h := div_pos hT hNPos
  have hh1 : h < 1 := (div_lt_one hNPos).mpr hTN
  have hlv : l < v := by dsimp [l, v]; linarith
  have hband (u : Real) (hu : abs (u - B) <= 1) :
      2 <= u /\ a <= (r : Real) / u /\ (r : Real) / u <= b := by
    have he := abs_le.mp hu
    have huPos : 0 < u := by dsimp [B] at he; linarith
    have hBm : 0 < B - 1 := by dsimp [B]; linarith
    refine And.intro (by dsimp [B] at he; linarith) (And.intro ?_ ?_)
    . exact hLower.trans (div_le_div_of_nonneg_left hrPos.le huPos (by linarith))
    . exact (div_le_div_of_nonneg_left hrPos.le hBm (by linarith)).trans hUpper
  have hdata (u : Real) (hu : abs (u - B) <= 1) :=
    hCompare r hrC' N hNC' u (hband u hu).1
      (by simpa only [abs_sub_comm] using hu) (hband u hu).2.2
  have hlNear : abs (l - B) <= 1 := by
    dsimp [l]
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hh]
    exact hh1.le
  have hvNear : abs (v - B) <= 1 := by
    dsimp [v]
    simpa only [add_sub_cancel_left, abs_of_pos hh] using hh1.le
  have hleft : law.densityRatio N r < law.referenceRatio r l := by
    have he := (abs_le.mp (hdata l hlNear).2.2).2
    have hm := InverseClockDetector.comparison_endpoint_margin
      (r : Real) (N : Real) l K a T hrPos hNPos (by linarith [(hband l hlNear).1])
      ha hK hrK (hband l hlNear).2.1 hTmargin
    have hdist : l - B = -h := by dsimp [l]; ring
    rw [hdist, abs_neg, abs_of_pos hh] at he
    change K * (h / l ^ 2 + 1 / ((r : Real) * N)) <
      (r : Real) / l ^ 2 * h at hm
    linarith
  have hright : law.referenceRatio r v < law.densityRatio N r := by
    have he := (abs_le.mp (hdata v hvNear).2.2).1
    have hm := InverseClockDetector.comparison_endpoint_margin
      (r : Real) (N : Real) v K a T hrPos hNPos (by linarith [(hband v hvNear).1])
      ha hK hrK (hband v hvNear).2.1 hTmargin
    have hdist : v - B = h := by dsimp [v]; ring
    rw [hdist, abs_of_pos hh] at he
    change K * (h / v ^ 2 + 1 / ((r : Real) * N)) <
      (r : Real) / v ^ 2 * h at hm
    linarith
  have hnear (u : Real) (hu : Set.Icc l v u) : abs (u - B) <= 1 := by
    apply abs_le.mpr
    change B - h <= u /\ u <= B + h at hu
    constructor <;> linarith
  have hc : ContinuousOn (law.referenceRatio r) (Set.Icc l v) := fun u hu =>
    (law.referenceRatio_continuousAt r u (hdata u (hnear u hu)).2.1).continuousWithinAt
  choose U hUI hU using intermediate_value_Icc' hlv.le hc (And.intro hright.le hleft.le)
  have hUIo : Set.Ioo l v U := by
    constructor
    . apply lt_of_le_of_ne hUI.1
      intro he
      subst U
      exact hleft.ne' hU
    . apply lt_of_le_of_ne hUI.2
      intro he
      subst U
      exact hright.ne hU
  refine Exists.intro U (And.intro ?_ (And.intro (hnear U hUI) (And.intro hU.symm ?_)))
  . change abs (U - B) < h
    apply abs_lt.mpr
    change B - h < U /\ U < B + h at hUIo
    constructor <;> linarith
  . intro V hV hVR
    have hUNear := hnear U hUI
    have hStrict : StrictAntiOn (law.referenceRatio r) (Set.Icc (B - 1) (B + 1)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      . intro u hu
        have hn : abs (u - B) <= 1 := abs_le.mpr (And.intro (by linarith [hu.1]) (by linarith [hu.2]))
        exact (law.referenceRatio_continuousAt r u (hdata u hn).2.1).continuousWithinAt
      . intro u hu
        have hn : abs (u - B) <= 1 := by
          have huI := interior_subset hu
          exact abs_le.mpr (And.intro (by linarith [huI.1]) (by linarith [huI.2]))
        have hbnd := hband u hn
        have hs := ((hSlope r hrS' u (by linarith [hbnd.1]) hbnd.2.2).2 hrKS).2
        change deriv (law.referenceRatio r) u <= -(r : Real) / (2 * u ^ 2) at hs
        exact hs.trans_lt (div_neg_of_neg_of_pos (by linarith)
          (mul_pos (by norm_num) (sq_pos_of_pos (by linarith [hbnd.1]))))
    apply hStrict.injOn
    . exact And.intro (by linarith [(abs_le.mp hV).1]) (by linarith [(abs_le.mp hV).2])
    . exact And.intro (by linarith [(abs_le.mp hUNear).1]) (by linarith [(abs_le.mp hUNear).2])
    . exact hVR.symm.trans hU.symm

end PrimeFactorOscillations.PrimeClockLaw
