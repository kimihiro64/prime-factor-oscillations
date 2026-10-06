/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PrimeFactorOscillations.Helpers.QuadraticProfileRatio
import PrimeFactorOscillations.Helpers.QuadraticProfileSlope

/-!
# Uniform linearization of the full prime-profile ratio

The actual paired finite-prefix error is combined with the full-profile
derivative estimate on a clock segment of length at most one.
This is the quantitative transfer used before taking RH-sensitive limits.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open BombieriVinogradov.ComplexAnalysis

theorem exists_profile_reference_linearization_error (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall B L : Real,
      2 <= L -> abs (B - L) <= 1 -> (r : Real) / L <= b ->
      abs (Nat.factorialConvolution law.realCoefficient (r - 1) B /
          Nat.factorialConvolution law.realCoefficient r B -
        Nat.factorialConvolution law.realCoefficient (r - 1) L /
          Nat.factorialConvolution law.realCoefficient r L -
        ((r : Real) / L ^ 2) * (L - B)) <= K / L ^ 2 * abs (B - L) := by
  choose rS Ks hrS hKs hSlope using
    law.exists_profile_reference_slope_bound (2 * b) (by positivity)
  choose rD hrD hDenom using
    law.exists_profile_normalized_coefficient_lower_bound (2 * b) (by positivity)
  refine Exists.intro (max rS rD) (Exists.intro (4 * Ks + 10 * b)
    (And.intro (hrS.trans_le (le_max_left _ _)) (And.intro (by positivity) ?_)))
  intro r hr B L hL hBL hRatio
  have hrS' : rS <= r := (le_max_left _ _).trans hr
  have hrD' : rD <= r := (le_max_right _ _).trans hr
  have hrPos : 0 < r := hrS.trans_le hrS'
  have hrReal : (0 : Real) < r := by exact_mod_cast hrPos
  have hLPos : 0 < L := by linarith
  have hrBound : (r : Real) <= b * L := by
    calc
      (r : Real) = ((r : Real) / L) * L := by field_simp [hLPos.ne']
      _ <= b * L := _root_.mul_le_mul_of_nonneg_right hRatio hLPos.le
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution law.realCoefficient (r - 1) u /
      Nat.factorialConvolution law.realCoefficient r u
  have hSegment (u : Real) (hu : Set.Icc (min B L) (max B L) u) :
      0 < u /\ L / 2 <= u /\ u <= 3 * L / 2 /\
      abs (u - L) <= 1 /\ (r : Real) / u <= 2 * b := by
    have hEnds := abs_le.mp hBL
    have hMin : L - 1 <= min B L := le_min (by linarith) (by linarith)
    have hMax : max B L <= L + 1 := max_le (by linarith) (by linarith)
    have hLo : L - 1 <= u := hMin.trans hu.1
    have hHi : u <= L + 1 := hu.2.trans hMax
    have huPos : 0 < u := by linarith
    have huHalf : L / 2 <= u := by linarith
    have huUpper : u <= 3 * L / 2 := by linarith
    have hR : (r : Real) <= 2 * b * u := by nlinarith
    have hQuot : (r : Real) / u <= 2 * b := by
      calc
        (r : Real) / u <= (2 * b * u) / u :=
          _root_.div_le_div_of_nonneg_right hR huPos.le
        _ = 2 * b := by field_simp [huPos.ne']
    exact And.intro huPos (And.intro huHalf (And.intro huUpper
      (And.intro (abs_le.mpr (And.intro (by linarith) (by linarith))) hQuot)))
  have hDiff (u : Real) (hu : Set.Icc (min B L) (max B L) u) :
      DifferentiableAt Real R u := by
    have hs := hSegment u hu
    have hLow := hDenom r hrD' ((r : Real) / u)
      (div_nonneg hrReal.le hs.1.le) hs.2.2.2.2
    have hA : 0 < Nat.normalizedDescFactorialPolynomial law.realCoefficient r
        ((r : Real) / u) :=
          lt_of_lt_of_le (half_pos (law.positiveLowerBound_pos (2 * b))) hLow
    exact (Nat.hasDerivAt_factorialConvolution_ratio law.realCoefficient r
      hrPos u hs.1.ne' hA.ne').differentiableAt
  have hDerivative (u : Real) (hu : Set.Icc (min B L) (max B L) u) :
      abs (deriv R u + (r : Real) / L ^ 2) <= (4 * Ks + 10 * b) / L ^ 2 := by
    have hs := hSegment u hu
    have huPos : 0 < u := hs.1
    have hSlopeU := (hSlope r hrS' u hs.1 hs.2.2.2.2).1
    change abs (deriv R u + (r : Real) / u ^ 2) <= Ks / u ^ 2 at hSlopeU
    have hReciprocal : abs ((r : Real) / L ^ 2 - (r : Real) / u ^ 2) <=
        10 * b / L ^ 2 := by
      have hIdentity : (r : Real) / L ^ 2 - (r : Real) / u ^ 2 =
          (r : Real) * (u - L) * (u + L) / (u ^ 2 * L ^ 2) := by
        field_simp [hLPos.ne', hs.1.ne']
        <;> ring
      rw [hIdentity, abs_div, abs_mul, abs_mul,
        abs_of_pos hrReal, abs_of_pos (by linarith : 0 < u + L),
        abs_of_pos (by positivity : 0 < u ^ 2 * L ^ 2)]
      calc
        (r : Real) * abs (u - L) * (u + L) / (u ^ 2 * L ^ 2) <=
            (b * L) * 1 * ((5 / 2 : Real) * L) / ((L / 2) ^ 2 * L ^ 2) := by
          gcongr
          . exact hs.2.2.2.1
          . linarith [hs.2.2.1]
          . exact hs.2.1
        _ = 10 * b / L ^ 2 := by field_simp [hLPos.ne']; ring
    have hSlopeBound : Ks / u ^ 2 <= 4 * Ks / L ^ 2 := by
      calc
        Ks / u ^ 2 <= Ks / (L / 2) ^ 2 := by gcongr; exact hs.2.1
        _ = 4 * Ks / L ^ 2 := by field_simp [hLPos.ne']; ring
    calc
      abs (deriv R u + (r : Real) / L ^ 2) =
          abs ((deriv R u + (r : Real) / u ^ 2) +
            ((r : Real) / L ^ 2 - (r : Real) / u ^ 2)) := by congr 1; ring
      _ <= abs (deriv R u + (r : Real) / u ^ 2) +
          abs ((r : Real) / L ^ 2 - (r : Real) / u ^ 2) := abs_add_le _ _
      _ <= Ks / u ^ 2 + 10 * b / L ^ 2 := _root_.add_le_add hSlopeU hReciprocal
      _ <= (4 * Ks + 10 * b) / L ^ 2 := by
        rw [add_div]
        exact _root_.add_le_add hSlopeBound le_rfl
  have hOrdered (x y : Real) (hxy : x < y)
      (hI : forall u : Real, Set.Icc x y u ->
        Set.Icc (min B L) (max B L) u) :
      abs (R x - R y - ((r : Real) / L ^ 2) * (y - x)) <=
        (4 * Ks + 10 * b) / L ^ 2 * (y - x) := by
    have hCont : ContinuousOn R (Set.Icc x y) := fun u hu =>
      (hDiff u (hI u hu)).continuousAt.continuousWithinAt
    have hDiffOn : DifferentiableOn Real R (Set.Ioo x y) := fun u hu =>
      (hDiff u (hI u (And.intro hu.1.le hu.2.le))).differentiableWithinAt
    choose u hu hMean using exists_deriv_eq_slope R hxy hCont hDiffOn
    have hMeanMul : deriv R u * (y - x) = R y - R x := by
      rw [hMean]
      field_simp [(sub_pos.mpr hxy).ne']
    have hBound := hDerivative u (hI u (And.intro hu.1.le hu.2.le))
    calc
      abs (R x - R y - ((r : Real) / L ^ 2) * (y - x)) =
          abs (-(deriv R u + (r : Real) / L ^ 2) * (y - x)) := by
        congr 1
        nlinarith only [hMeanMul]
      _ = abs (deriv R u + (r : Real) / L ^ 2) * (y - x) := by
        rw [abs_mul, abs_neg, abs_of_pos (sub_pos.mpr hxy)]
      _ <= (4 * Ks + 10 * b) / L ^ 2 * (y - x) :=
        _root_.mul_le_mul_of_nonneg_right hBound (sub_pos.mpr hxy).le
  change abs (R B - R L - ((r : Real) / L ^ 2) * (L - B)) <=
    (4 * Ks + 10 * b) / L ^ 2 * abs (B - L)
  by_cases hEq : B = L
  . simp only [hEq, sub_self, mul_zero, abs_zero]
    exact le_rfl
  . cases lt_or_gt_of_ne hEq with
    | inl hlt =>
      have h := hOrdered B L hlt (by
        intro u hu
        simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hu)
      rw [abs_of_neg (sub_neg.mpr hlt)]
      convert h using 1 <;> ring
    | inr hgt =>
      have h := hOrdered L B hgt (by
        intro u hu
        simpa only [min_eq_right hgt.le, max_eq_left hgt.le] using hu)
      have hNeg : R B - R L - ((r : Real) / L ^ 2) * (L - B) =
          -(R L - R B - ((r : Real) / L ^ 2) * (B - L)) := by ring
      rw [hNeg, abs_neg, abs_of_pos (sub_pos.mpr hgt)]
      exact h

theorem exists_prefixProfile_ratio_linearization (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 < b) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall B L : Real, 2 <= L -> abs (B - L) <= 1 -> (r : Real) / L <= b ->
      0 < Nat.factorialConvolution
        (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r B /\
      0 < Nat.factorialConvolution law.realCoefficient r L /\
      abs (Nat.factorialConvolution
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) (r - 1) B /
        Nat.factorialConvolution
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r B -
        Nat.factorialConvolution law.realCoefficient (r - 1) L /
          Nat.factorialConvolution law.realCoefficient r L -
        ((r : Real) / L ^ 2) * (L - B)) <=
          K * (abs (L - B) / L ^ 2 + 1 / ((r : Real) * (N : Real))) := by
  choose rR KR hrR hKR hReference using
    law.exists_profile_reference_linearization_error b hb
  choose rP N0 KP hrP hN0 hKP hPrefix using
    law.exists_prefixProfile_factorialConvolution_ratio_error (2 * b) (by positivity)
  refine Exists.intro (max rR rP) (Exists.intro N0 (Exists.intro (KR + KP)
    (And.intro (hrR.trans_le (le_max_left _ _))
      (And.intro hN0 (And.intro (by positivity) ?_)))))
  intro r hr N hN B L hL hBL hRatio
  have hrR' : rR <= r := (le_max_left _ _).trans hr
  have hrP' : rP <= r := (le_max_right _ _).trans hr
  have hrPos : 0 < r := hrR.trans_le hrR'
  have hrReal : (0 : Real) < r := by exact_mod_cast hrPos
  have hNPos : (0 : Real) < N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (hN0.trans hN))
  have hLPos : 0 < L := by linarith
  have hEnds := abs_le.mp hBL
  have hBPos : 0 < B := by linarith
  have hBHalf : L / 2 <= B := by linarith
  have hrBound : (r : Real) <= b * L := by
    calc
      (r : Real) = ((r : Real) / L) * L := by field_simp [hLPos.ne']
      _ <= b * L := _root_.mul_le_mul_of_nonneg_right hRatio hLPos.le
  have hRBound : (r : Real) <= 2 * b * B := by nlinarith
  have hRatioB : (r : Real) / B <= 2 * b := by
    calc
      (r : Real) / B <= (2 * b * B) / B :=
        _root_.div_le_div_of_nonneg_right hRBound hBPos.le
      _ = 2 * b := by field_simp [hBPos.ne']
  have hPB := hPrefix r hrP' N hN B hBPos hRatioB
  have hPL := hPrefix r hrP' N hN L hLPos (hRatio.trans (by linarith))
  have hRef := hReference r hrR' B L hL hBL hRatio
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution law.realCoefficient (r - 1) u /
      Nat.factorialConvolution law.realCoefficient r u
  let RN : Real := Nat.factorialConvolution
    (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) (r - 1) B /
      Nat.factorialConvolution
        (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r B
  have hError : abs (RN - R B) <= KP / ((r : Real) * (N : Real)) := hPB.2.2
  change abs (R B - R L - ((r : Real) / L ^ 2) * (L - B)) <=
    KR / L ^ 2 * abs (B - L) at hRef
  refine And.intro hPB.1 (And.intro hPL.2.1 ?_)
  change abs (RN - R L - ((r : Real) / L ^ 2) * (L - B)) <= _
  calc
    abs (RN - R L - ((r : Real) / L ^ 2) * (L - B)) =
        abs ((RN - R B) + (R B - R L - ((r : Real) / L ^ 2) * (L - B))) := by
      congr 1
      ring
    _ <= abs (RN - R B) + abs (R B - R L - ((r : Real) / L ^ 2) * (L - B)) :=
      abs_add_le _ _
    _ <= KP / ((r : Real) * (N : Real)) + KR / L ^ 2 * abs (B - L) :=
      _root_.add_le_add hError hRef
    _ = KP * (1 / ((r : Real) * (N : Real))) + KR * (abs (L - B) / L ^ 2) := by
      rw [abs_sub_comm B L]
      ring
    _ <= (KR + KP) * (abs (L - B) / L ^ 2 + 1 / ((r : Real) * (N : Real))) := by
      have hInverse : (0 : Real) <= 1 / ((r : Real) * (N : Real)) := by positivity
      have hDelta : (0 : Real) <= abs (L - B) / L ^ 2 := by positivity
      nlinarith [mul_nonneg hKR hInverse, mul_nonneg hKP hDelta]

end PrimeFactorOscillations.QuadraticPrimeLaw
