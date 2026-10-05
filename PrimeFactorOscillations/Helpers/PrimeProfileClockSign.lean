/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PrimeFactorOscillations.Helpers.PrimeProfileRatio
import PrimeFactorOscillations.Helpers.PrimeProfileSlope

/-!
# Quantitative clock-to-ratio sign transfer

A controlled reference secant and the actual finite-prefix error preserve
both signs once the clock separation exceeds the uniform inverse-cutoff error.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

theorem exists_primeProfile_reference_secant_bounds
    (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists r0 : Nat, 0 < r0 /\ forall r : Nat, r0 <= r ->
      forall B L : Real,
      (forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) ->
      exists q : Real, a ^ 2 / (2 * (r : Real)) <= q /\
        q <= 3 * b ^ 2 / (2 * (r : Real)) /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) B /
          Nat.factorialConvolution primeProfileRealCoefficient r B -
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L = q * (L - B) := by
  have hb : 0 <= b := ha.le.trans hab
  obtain hs := exists_primeProfile_reference_slope_bound b hb
  choose rS K hrS hK hslope using hs
  obtain hd := exists_primeProfile_normalized_coefficient_lower_bound b hb
  choose rD hrD hdenom using hd
  choose n0 hn0 using exists_nat_gt (2 * K)
  refine Exists.intro (max rD (max rS (n0 + 1))) (And.intro
    (hrD.trans_le (le_max_left _ _)) ?_)
  intro r hr B L hsegment
  have hrD' : rD <= r := (le_max_left _ _).trans hr
  have hrS' : rS <= r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hn' : n0 + 1 <= r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hrpos : 0 < r := hrD.trans_le hrD'
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  have hnR : (n0 : Real) < r := by exact_mod_cast (Nat.lt_succ_self n0).trans_le hn'
  have hlarge : 2 * K <= (r : Real) := (hn0.trans hnR).le
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
      Nat.factorialConvolution primeProfileRealCoefficient r u
  have hordered (x y : Real) (hxy : x < y)
      (hI : forall u : Real, Set.Icc x y u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) :
      exists q : Real, a ^ 2 / (2 * (r : Real)) <= q /\
        q <= 3 * b ^ 2 / (2 * (r : Real)) /\ R x - R y = q * (y - x) := by
    have hdiff (u : Real) (huI : Set.Icc x y u) : DifferentiableAt Real R u := by
      have hu := hI u huI
      have hlow := hdenom r hrD' ((r : Real) / u)
        (div_nonneg hrR.le hu.1.le) hu.2.2
      have hA : 0 < Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r
          ((r : Real) / u) := lt_of_lt_of_le (by positivity) hlow
      exact (Nat.hasDerivAt_factorialConvolution_ratio primeProfileRealCoefficient r
        hrpos u hu.1.ne' hA.ne').differentiableAt
    have hcont : ContinuousOn R (Set.Icc x y) := fun u hu =>
      (hdiff u hu).continuousAt.continuousWithinAt
    have hdiffOn : DifferentiableOn Real R (Set.Ioo x y) := fun u hu =>
      (hdiff u (And.intro hu.1.le hu.2.le)).differentiableWithinAt
    obtain hm := exists_deriv_eq_slope R hxy hcont hdiffOn
    choose u huI hmean using hm
    have hu := hI u (And.intro huI.1.le huI.2.le)
    have hupos : 0 < u := hu.1
    have htpos : 0 <= (r : Real) / u := div_nonneg hrR.le hupos.le
    have hs := (hslope r hrS' u hu.1 hu.2.2).2 hlarge
    change -(3 * (r : Real)) / (2 * u ^ 2) <= deriv R u /\
      deriv R u <= -(r : Real) / (2 * u ^ 2) at hs
    simp only [neg_div] at hs
    have hlo : a ^ 2 / (2 * (r : Real)) <= (r : Real) / (2 * u ^ 2) := by
      calc
        a ^ 2 / (2 * (r : Real)) <= ((r : Real) / u) ^ 2 / (2 * (r : Real)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          gcongr
          exact hu.2.1
        _ = (r : Real) / (2 * u ^ 2) := by field_simp [hrR.ne', hupos.ne']
    have hhi : 3 * (r : Real) / (2 * u ^ 2) <= 3 * b ^ 2 / (2 * (r : Real)) := by
      calc
        3 * (r : Real) / (2 * u ^ 2) =
            3 * ((r : Real) / u) ^ 2 / (2 * (r : Real)) := by
          field_simp [hrR.ne', hupos.ne']
        _ <= 3 * b ^ 2 / (2 * (r : Real)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          gcongr
          exact hu.2.2
    refine Exists.intro (-deriv R u) (And.intro (by linarith only [hs.2, hlo])
      (And.intro (by linarith only [hs.1, hhi]) ?_))
    rw [hmean]
    have hxy0 : Not (y - x = 0) := sub_ne_zero.mpr hxy.ne'
    field_simp
    ring
  by_cases hBL : B = L
  case pos =>
    have hupper : a ^ 2 / (2 * (r : Real)) <= 3 * b ^ 2 / (2 * (r : Real)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hsq : a ^ 2 <= b ^ 2 := by gcongr
      nlinarith [sq_nonneg b]
    refine Exists.intro (a ^ 2 / (2 * (r : Real)))
      (And.intro le_rfl (And.intro hupper ?_))
    simp only [hBL, sub_self, mul_zero]
  case neg =>
    cases lt_or_gt_of_ne hBL with
    | inl hlt =>
      have hI : forall u : Real, Set.Icc B L u ->
          0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b := by
        simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hsegment
      exact hordered B L hlt hI
    | inr hgt =>
      have hI : forall u : Real, Set.Icc L B u ->
          0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b := by
        simpa only [min_eq_right hgt.le, max_eq_left hgt.le] using hsegment
      obtain hq := hordered L B hgt hI
      choose q hqlo hqhi heq using hq
      refine Exists.intro q (And.intro hqlo (And.intro hqhi ?_))
      change R B - R L = q * (L - B)
      linarith

theorem exists_primePrefixProfile_clock_sign_transfer
    (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists r0 N0 : Nat, exists C : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall B L : Real,
      (forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) ->
      0 < Nat.factorialConvolution
        (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
      (C / (N : Real) < L - B ->
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L <
          Nat.factorialConvolution
              (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1) B /
            Nat.factorialConvolution
              (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B) /\
      (L - B < -C / (N : Real) ->
        Nat.factorialConvolution
            (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1) B /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) := by
  have hb : 0 <= b := ha.le.trans hab
  obtain hs := exists_primeProfile_reference_secant_bounds a b ha hab
  choose rS hrS hsecant using hs
  obtain he := exists_primePrefixProfile_factorialConvolution_ratio_error b hb
  choose rP N0 K hrP hN0 hK herror using he
  let C := 2 * K / a ^ 2
  have hC : 0 <= C := by dsimp [C]; positivity
  refine Exists.intro (max rS rP) (Exists.intro N0 (Exists.intro C
    (And.intro (hrS.trans_le (le_max_left _ _)) (And.intro hN0 (And.intro hC ?_)))))
  intro r hr N hN B L hsegment
  have hrS' : rS <= r := (le_max_left _ _).trans hr
  have hrP' : rP <= r := (le_max_right _ _).trans hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrS.trans_le hrS'
  have hNR : (0 : Real) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hN0.trans hN)
  have hB := hsegment B (And.intro (min_le_left _ _) (le_max_left _ _))
  have hL := hsegment L (And.intro (min_le_right _ _) (le_max_right _ _))
  have heB := herror r hrP' N hN B hB.1 hB.2.2
  have heL := herror r hrP' N hN L hL.1 hL.2.2
  obtain hq := hsecant r hrS' B L hsegment
  choose q hqlo hqhi hqeq using hq
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
      Nat.factorialConvolution primeProfileRealCoefficient r u
  let RN : Real := Nat.factorialConvolution
    (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1) B /
      Nat.factorialConvolution
        (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r B
  have herr : abs (RN - R B) <= K / ((r : Real) * (N : Real)) := heB.2.2
  change R B - R L = q * (L - B) at hqeq
  have hgain (w : Real) (hw : C / (N : Real) < w) :
      K / ((r : Real) * (N : Real)) < a ^ 2 / (2 * (r : Real)) * w := by
    have h := mul_lt_mul_of_pos_left hw (by positivity : 0 < a ^ 2 / (2 * (r : Real)))
    have hid : a ^ 2 / (2 * (r : Real)) * (C / (N : Real)) =
        K / ((r : Real) * (N : Real)) := by
      dsimp [C]
      field_simp
    rwa [hid] at h
  have hpositive : C / (N : Real) < L - B -> R L < RN := by
    intro hF
    have hFpos : 0 <= L - B := (div_nonneg hC hNR.le).trans hF.le
    have hqF := mul_le_mul_of_nonneg_right hqlo hFpos
    have hg := hgain (L - B) hF
    have hlow := (abs_le.mp herr).1
    linarith
  have hnegative : L - B < -C / (N : Real) -> RN < R L := by
    intro hF
    rw [neg_div] at hF
    have hF' : C / (N : Real) < -(L - B) := by linarith only [hF]
    have hFpos : 0 <= -(L - B) := (div_nonneg hC hNR.le).trans hF'.le
    have hqF := mul_le_mul_of_nonneg_right hqlo hFpos
    have hg := hgain (-(L - B)) hF'
    have hupp := (abs_le.mp herr).2
    nlinarith
  exact And.intro heB.1 (And.intro heL.2.1 (And.intro hpositive hnegative))

end PrimeFactorOscillations

