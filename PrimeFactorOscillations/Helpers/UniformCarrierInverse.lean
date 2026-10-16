/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierGeometry
import PrimeFactorOscillations.Helpers.UniformCarrierPerturbation
import PrimeFactorOscillations.Helpers.UniformCarrierStability

/-!
# Uniform Carrier Inverse

Uniform existence and localization of perturbed carrier inverses with explicit band membership.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

theorem negative_slope (f : Real -> Real) (u r a K : Real)
    (hu : 0 < u) (hr : 0 < r) (ha : 0 < a) (hK : 0 <= K)
    (haBand : a <= r / u) (hrK : 2 * K <= r)
    (hSlope : abs (deriv f u + r / u ^ 2) <= K / u ^ 2) :
    deriv f u <= -(a ^ 2 / (2 * r)) := by
  have hpay : K / u ^ 2 <= r / (2 * u ^ 2) := by
    calc
      _ <= (r / 2) / u ^ 2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg u)
      _ = _ := by ring
  have hneg : deriv f u <= -(r / (2 * u ^ 2)) := by
    have he := (abs_le.mp hSlope).2
    have hid : r / u ^ 2 = 2 * (r / (2 * u ^ 2)) := by ring
    linarith only [he, hpay, hid]
  have hbu := mul_le_mul_of_nonneg_right haBand hu.le
  have hband : a * u <= r := by
    convert hbu using 1 <;> field_simp [hu.ne']
  have hsquare : a ^ 2 * u ^ 2 <= r ^ 2 := by
    nlinarith [mul_nonneg ha.le hu.le]
  have hid1 : a ^ 2 / (2 * r) = (a ^ 2 * u ^ 2) / (2 * r * u ^ 2) := by
    field_simp [hu.ne', hr.ne']
  have hid2 : r / (2 * u ^ 2) = r ^ 2 / (2 * r * u ^ 2) := by
    field_simp [hu.ne', hr.ne']
  apply hneg.trans
  apply neg_le_neg
  rw [hid1, hid2]
  exact div_le_div_of_nonneg_right hsquare (by positivity)

theorem exists_uniform_reference_inverse (base : PrimeClockLaw)
    (hbs : base.scale = 1) (hbe : base.error = 0)
    (a : Real) (ha : 0 < a) (b : Real) (hb : 0 < b) :
    exists r0 N0 : Nat, exists eps C : Real,
      0 < r0 /\ 1 <= N0 /\ 0 < eps /\ 0 < C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      3 <= base.arithmeticClock N ->
      a <= (r : Real) / (base.arithmeticClock N + 1) ->
      (r : Real) / (base.arithmeticClock N - 1) <= b ->
      forall A : PrimeClockLaw, A.scale = 1 -> A.error = 0 ->
      forall T : Finset Nat.Primes, T <= primeProfilePrefixSet N ->
      (forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
        A.weight p = base.weight p /\ A.compensator p = base.compensator p) ->
      T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) <= eps ->
      abs (A.arithmeticClock N - base.arithmeticClock N) <= 1 / 4 ->
      exists U : Real,
        abs (U - A.arithmeticClock N) <=
          C * T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) /\
        base.prefixEsymm N r > 0 /\
        A.densityRatio N r = prefixRatio base N r U /\
        (forall V : Real, abs (V - base.arithmeticClock N) <= 1 ->
          A.densityRatio N r = prefixRatio base N r V -> V = U) /\
        abs (U - base.arithmeticClock N) <= 1 / 2 := by
  choose rG N0 d M K hrG hN0 hd hM hK hGeom using
    exists_finite_reference_geometry base hbs hbe b hb.le
  choose Rrank hRrank using exists_nat_gt (2 * K)
  let R := b + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hbR : b < R := by dsimp [R]; linarith
  let q := 1 - b / R
  have hq : 0 < q := sub_pos.mpr ((div_lt_one hR).mpr hbR)
  let Z := 2 * kernelConstant R * productBound R ^ 2
  have hZ : 0 <= Z := by dsimp [Z, kernelConstant]; positivity
  let CV := Z / q
  let CD := Z / (R * q ^ 2)
  have hCV : 0 <= CV := div_nonneg hZ hq.le
  have hCD : 0 <= CD := by dsimp [CD]; positivity
  let Q := b ^ 2 * (CD / (d / 2) + M * CV / ((d / 2) * (d / 2)))
  have hQ : 0 <= Q := by dsimp [Q]; positivity
  let H := 4 * (Q + 1) / a ^ 2
  have hH : 0 < H := by dsimp [H]; positivity
  let eps := min (d / (2 * (CV + 1))) (1 / (4 * (H + 1)))
  have hEps : 0 < eps := by dsimp [eps]; positivity
  refine Exists.intro (max rG Rrank) (Exists.intro N0 (Exists.intro eps
    (Exists.intro H (And.intro (hrG.trans_le (le_max_left _ _))
      (And.intro hN0 (And.intro hEps (And.intro hH ?_)))))))
  intro r hr N hN hB hLower hUpper A hAs hAe T hT hSame hDelta hClock
  let B := base.arithmeticClock N
  let BA := A.arithmeticClock N
  let delta := T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)
  have hdelta : 0 <= delta := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hrG' : rG <= r := (le_max_left _ _).trans hr
  have hrPos : 0 < r := hrG.trans_le hrG'
  have hrR : (0 : Real) < r := by exact_mod_cast hrPos
  have hRr : Rrank <= r := (le_max_right _ _).trans hr
  have hrK : 2 * K <= (r : Real) :=
    hRrank.le.trans (by exact_mod_cast hRr)
  have hsmall : CV * delta <= d / 2 := by
    have he1 : delta <= d / (2 * (CV + 1)) := hDelta.trans (min_le_left _ _)
    have hh := mul_le_mul_of_nonneg_left he1 (by linarith : 0 <= CV + 1)
    have hc : (CV + 1) * (d / (2 * (CV + 1))) = d / 2 := by field_simp
    rw [hc] at hh
    nlinarith
  have hRadius : H * delta <= 1 / 4 := by
    have he1 : delta <= 1 / (4 * (H + 1)) := hDelta.trans (min_le_right _ _)
    have hh := mul_le_mul_of_nonneg_left he1 (by linarith : 0 <= H + 1)
    have hc : (H + 1) * (1 / (4 * (H + 1))) = (1 / 4 : Real) := by field_simp
    rw [hc] at hh
    nlinarith
  have hband (u : Real) (hu : abs (u - B) <= 1) :
      2 <= u /\ a <= (r : Real) / u /\ (r : Real) / u <= b := by
    have he := abs_le.mp hu
    have huPos : 0 < u := by change 3 <= B at hB; linarith
    have hBm : 0 < B - 1 := by change 3 <= B at hB; linarith
    refine And.intro (by change 3 <= B at hB; linarith) (And.intro ?_ ?_)
    . exact hLower.trans (div_le_div_of_nonneg_left hrR.le huPos (by linarith))
    . exact (div_le_div_of_nonneg_left hrR.le hBm (by linarith)).trans hUpper
  have hg (u : Real) (hu : abs (u - B) <= 1) :=
    hGeom r hrG' N hN u (by linarith [(hband u hu).1]) (hband u hu).2.2
  have hBANear : abs (BA - B) <= 1 := hClock.trans (by norm_num)
  have hBApos : 0 < BA := by linarith [(hband BA hBANear).1]
  have hcoeff (j : Nat) :
      norm (BombieriVinogradov.ComplexAnalysis.taylorCoefficient (A.complexPrefix N) 0 j -
        BombieriVinogradov.ComplexAnalysis.taylorCoefficient (base.complexPrefix N) 0 j) <=
          (Z * delta) / R ^ j :=
    finite_coefficient_comparison R hR A base hAs hAe hbs hbe N T hT hSame j
  have hSmallTotal : (Z * delta) / (1 - b / R) <= d / 2 := by
    convert hsmall using 1 <;> dsimp [CV, q] <;> ring
  have hratio := ratio_error_of_coefficient_bound A base N r hrPos BA b R (Z * delta)
    d M hBApos (hband BA hBANear).2.2 hbR (mul_nonneg hZ hdelta) hd hM
    hcoeff (hg BA hBANear).1 hSmallTotal (hg BA hBANear).2.2.1
  have hError : abs (A.densityRatio N r - prefixRatio base N r BA) <=
      Q * delta / (r : Real) := by
    rw [A.densityRatio_eq_factorialConvolution N r]
    change abs (prefixRatio A N r BA - prefixRatio base N r BA) <= _
    convert hratio.2 using 1 <;> dsimp [Q, CV, CD, q] <;> ring
  have hDiff (u : Real) (hu : Membership.mem (Set.Icc (B - 1) (B + 1)) u) :
      DifferentiableAt Real (prefixRatio base N r) u := by
    have hn : abs (u - B) <= 1 :=
      abs_le.mpr (And.intro (by linarith [hu.1]) (by linarith [hu.2]))
    exact (hg u hn).2.2.2.1
  have hSlope (u : Real) (hu : Membership.mem (Set.Icc (B - 1) (B + 1)) u) :
      deriv (prefixRatio base N r) u <= -(a ^ 2 / (2 * (r : Real))) := by
    have hn : abs (u - B) <= 1 :=
      abs_le.mpr (And.intro (by linarith [hu.1]) (by linarith [hu.2]))
    exact negative_slope (prefixRatio base N r) u (r : Real) a K
      (by linarith [(hband u hn).1]) hrR ha hK (hband u hn).2.1 hrK (hg u hn).2.2.2.2
  have hds : 0 < a ^ 2 / (2 * (r : Real)) := by positivity
  have hBasePos : 0 < base.prefixEsymm N r := by
    rw [<- base.prefix_factorialConvolution_eq_esymm N r]
    exact (hg B (by simp)).2.1
  by_cases hz : delta = 0
  . have hEq : A.densityRatio N r = prefixRatio base N r BA := by
      have he : abs (A.densityRatio N r - prefixRatio base N r BA) <= 0 := by simpa only [hz, mul_zero, zero_div] using hError
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))
    refine Exists.intro BA (And.intro (by
      change abs (BA - BA) <= H * delta
      simp only [sub_self, abs_zero, hz, mul_zero, le_refl])
      (And.intro hBasePos (And.intro hEq (And.intro ?_ (hClock.trans (by norm_num))))))
    intro V hV hVR
    have hAnti : StrictAntiOn (prefixRatio base N r) (Set.Icc (B - 1) (B + 1)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      . intro u hu
        exact (hDiff u hu).continuousAt.continuousWithinAt
      . intro u hu
        exact (hSlope u (interior_subset hu)).trans_lt (by linarith)
    apply hAnti.injOn
    . exact And.intro (by linarith [(abs_le.mp hV).1]) (by linarith [(abs_le.mp hV).2])
    . exact And.intro (by linarith [(abs_le.mp hBANear).1]) (by linarith [(abs_le.mp hBANear).2])
    . exact hVR.symm.trans hEq
  . have hdeltapos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hz)
    have hh : 0 < H * delta := mul_pos hH hdeltapos
    have hClock' : abs (BA - B) <= 1 / 4 := hClock
    have hEnds := abs_le.mp hClock'
    have hl : B - 1 <= BA - H * delta := by linarith only [hEnds.1, hRadius]
    have hu : BA + H * delta <= B + 1 := by linarith only [hEnds.2, hRadius]
    have hMargin : Q * delta / (r : Real) <
        (a ^ 2 / (2 * (r : Real))) * (H * delta) := by
      have hid : (a ^ 2 / (2 * (r : Real))) * (H * delta) =
          (2 * (Q + 1) * delta) / (r : Real) := by
        dsimp [H]
        field_simp [ha.ne', hrR.ne']
        ring
      rw [hid]
      apply div_lt_div_of_pos_right _ hrR
      nlinarith only [mul_nonneg hQ hdeltapos.le, hdeltapos]
    choose U hU hRoot hUnique using root_stability
      (prefixRatio base N r) (B - 1) (B + 1) BA (A.densityRatio N r)
      (a ^ 2 / (2 * (r : Real))) (H * delta) (Q * delta / (r : Real))
      hds hh hl hu hDiff hSlope hError hMargin
    have hUBand : abs (U - B) <= 1 / 2 := by
      calc
        abs (U - B) = abs ((U - BA) + (BA - B)) := by congr 1; ring
        _ <= abs (U - BA) + abs (BA - B) := abs_add_le _ _
        _ <= H * delta + 1 / 4 := _root_.add_le_add hU.le hClock'
        _ <= 1 / 2 := by linarith only [hRadius]
    refine Exists.intro U (And.intro hU.le (And.intro hBasePos
      (And.intro hRoot.symm (And.intro ?_ hUBand))))
    intro V hV hVR
    apply hUnique V
    . exact And.intro (by linarith [(abs_le.mp hV).1]) (by linarith [(abs_le.mp hV).2])
    . exact hVR.symm

end PrimeFactorOscillations.UniformCarrier
