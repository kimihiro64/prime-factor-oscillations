/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSubsetRigidity

/-! # The optimal residual coefficient for squarefree prime differences -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

def primeModNineClass (X : Nat) : Finset Nat :=
  (oddPrimeVertices X).filter (fun p : Nat => (p : ZMod 9) = 1)

private def spectralWitnessResidueCount (X N r : Nat) : Nat :=
  ((Nat.primesBelow (X + 1)).filter (fun p : Nat => (p : ZMod N) = (r : ZMod N))).card

private theorem nine_class_full_primes (X : Nat) :
    primeModNineClass X =
      (Nat.primesBelow (X + 1)).filter (fun p : Nat => (p : ZMod 9) = 1) := by
  unfold primeModNineClass oddPrimeVertices
  rw [Finset.filter_erase]
  have h : Not ((2 : ZMod 9) = 1) := by decide
  apply Finset.ext
  intro p
  simp only [Finset.mem_erase, Finset.mem_filter]
  constructor
  { exact fun hp => hp.2 }
  { intro hp
    refine And.intro ?_ hp
    intro heq
    subst p
    exact h hp.2 }

private theorem nine_unit_count (X : Nat) (hX : 3 <= X) :
    ((Nat.primesBelow (X + 1)).filter (fun p : Nat => IsUnit (p : ZMod 9))).card =
      (oddPrimeVertices X).card := by
  let S := Nat.primesBelow (X + 1)
  have hFilter : S.filter (fun p : Nat => IsUnit (p : ZMod 9)) = S.erase 3 := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    { intro h
      refine And.intro ?_ h.1
      intro heq
      subst p
      exact (show Not (IsUnit (3 : ZMod 9)) from by decide) h.2 }
    { intro h
      refine And.intro h.2 ?_
      have hp : Nat.Prime p := (Nat.mem_primesBelow.mp h.2).2
      simpa only [Nat.reducePow] using
        prime_square_residue_isUnit p 3 hp Nat.prime_three h.1 }
  have hTwo : Membership.mem S 2 :=
    Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_two)
  have hThree : Membership.mem S 3 :=
    Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three)
  have hc2 := Finset.card_erase_add_one hTwo
  have hc3 := Finset.card_erase_add_one hThree
  change (S.filter (fun p : Nat => IsUnit (p : ZMod 9))).card = (S.erase 2).card
  rw [hFilter]
  omega

private theorem nine_vertex_count_pos {X : Nat} (hX : 3 <= X) :
    (0 : Real) < (oddPrimeVertices X).card := by
  apply Nat.cast_pos.mpr
  apply Finset.card_pos.mpr
  refine Exists.intro 3 ?_
  exact Finset.mem_erase.mpr (And.intro (by decide)
    (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three)))

private theorem nine_parity_indicator (p : Nat) (hp : Nat.Prime p) :
    primeResidueSign p * (if (p : ZMod 9) = 1 then (1 : Real) else 0) =
      (if (p : ZMod 36) = 1 then 1 else 0) -
        (if (p : ZMod 36) = 19 then 1 else 0) := by
  have h4 : ((p : ZMod 4) = 1) <-> p % 4 = 1 :=
    ZMod.natCast_eq_natCast_iff p 1 4
  have h9 : ((p : ZMod 9) = 1) <-> p % 9 = 1 :=
    ZMod.natCast_eq_natCast_iff p 1 9
  have h1 : ((p : ZMod 36) = 1) <-> p % 36 = 1 :=
    ZMod.natCast_eq_natCast_iff p 1 36
  have h19 : ((p : ZMod 36) = 19) <-> p % 36 = 19 :=
    ZMod.natCast_eq_natCast_iff p 19 36
  simp only [primeResidueSign, h4, h9, h1, h19]
  cases hp.eq_two_or_odd with
  | inl h =>
    subst p
    norm_num
  | inr hOdd =>
    by_cases ha : p % 36 = 1
    { have hNine : p % 9 = 1 := by omega
      have hFour : p % 4 = 1 := by omega
      have hb : Not (p % 36 = 19) := by omega
      simp [ha, hNine, hFour] }
    { by_cases hb : p % 36 = 19
      { have hNine : p % 9 = 1 := by omega
        have hFour : Not (p % 4 = 1) := by omega
        simp [hb, hNine, hFour] }
      { have hNine : Not (p % 9 = 1) := by omega
        simp [ha, hb, hNine] } }

private theorem nine_bias_sum (X : Nat) :
    (primeModNineClass X).sum primeResidueSign =
      (spectralWitnessResidueCount X 36 1 : Real) -
        (spectralWitnessResidueCount X 36 19 : Real) := by
  rw [nine_class_full_primes, Finset.sum_filter]
  calc
    _ = (Nat.primesBelow (X + 1)).sum (fun p : Nat =>
        (if (p : ZMod 36) = 1 then (1 : Real) else 0) -
          (if (p : ZMod 36) = 19 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h := nine_parity_indicator p (Nat.mem_primesBelow.mp hp).2
      simpa only [mul_ite, mul_one, mul_zero] using h
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      norm_num only [Finset.sum_boole, spectralWitnessResidueCount, Nat.cast_ofNat]

/-- The actual residue-class witness has no squarefree differences. -/
theorem prime_mod_nine_class_independent (X : Nat) :
    SquarefreeDifferenceIndependent (primeModNineClass X) := by
  intro p hp q hq hpq
  have hCast : (p : ZMod 9) = (q : ZMod 9) :=
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hBad : Not (forall ell : Nat, Nat.Prime ell ->
      Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)))) := by
    intro h
    apply h 3 Nat.prime_three
    simpa only [Nat.reducePow] using hCast
  intro hSquare
  have hK : primeSquarefreeDifferenceKernel p q = 1 := by
    simp [primeSquarefreeDifferenceKernel, hSquare]
  rw [primeSquarefreeDifferenceKernel_eq_prime_avoidance] at hK
  simp [hBad] at hK


private def spectralWitnessError (C : Real) (N X : Nat) : Real :=
  C * (X : Real) ^ (7 / 8 : Real) *
    (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2

private theorem witness_error_ratio (C : Real) (N : Nat) (hN : 1 <= N) :
    Tendsto (fun X : Nat => spectralWitnessError C N X /
      ((oddPrimeVertices X).card : Real)) atTop (nhds (0 : Real)) := by
  have hLog : 0 <= Real.log (N : Real) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have h := tendsto_rpow_logshift_pow_div_oddPrimeCount (7 / 8) (1 + Real.log N)
    (by norm_num) (by linarith) 2
  simpa only [spectralWitnessError, mul_zero, mul_div_assoc, mul_assoc] using h.const_mul C

/-- The independent modulo-nine witness has relative prime density one sixth. -/
theorem tendsto_prime_mod_nine_class_density :
    Tendsto (fun X : Nat => primeSubsetDensity X (primeModNineClass X))
      atTop (nhds (1 / 6 : Real)) := by
  choose C hC using exists_primeCharacterSum_le_seven_eighths
  have hCpos : 0 < C := hC.1
  have hError := witness_error_ratio C 9 (by decide)
  have hBound : Filter.Eventually (fun X : Nat =>
      abs (primeSubsetDensity X (primeModNineClass X) - 1 / 6) <=
        spectralWitnessError C 9 X / ((oddPrimeVertices X).card : Real)) atTop := by
    filter_upwards [eventually_ge_atTop (3 : Nat)] with X hX
    have hn := nine_vertex_count_pos hX
    have hE : 0 <= spectralWitnessError C 9 X := by
      dsimp [spectralWitnessError]
      positivity
    have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      (Nat.primesBelow (X + 1)) (fun p : Nat => (p : ZMod 9))
      (1 : Units (ZMod 9)) (spectralWitnessError C 9 X) hE
      (fun chi hchi => hC.2 chi hchi X)
    change abs ((((Nat.primesBelow (X + 1)).filter
        (fun p : Nat => (p : ZMod 9) = 1)).card : Real) -
      (((Nat.primesBelow (X + 1)).filter
        (fun p : Nat => IsUnit (p : ZMod 9))).card : Real) /
          ((9 : Nat).totient : Real)) <= spectralWitnessError C 9 X at h
    rw [<- nine_class_full_primes X, nine_unit_count X hX,
      show (9 : Nat).totient = 6 from by decide] at h
    norm_num only [Nat.cast_ofNat] at h
    have hIdentity : primeSubsetDensity X (primeModNineClass X) - 1 / 6 =
        (((primeModNineClass X).card : Real) -
          ((oddPrimeVertices X).card : Real) / 6) /
            ((oddPrimeVertices X).card : Real) := by
      unfold primeSubsetDensity
      field_simp [hn.ne']
    rw [hIdentity, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right h hn.le
  have hz : Filter.Eventually (fun X : Nat =>
      0 <= abs (primeSubsetDensity X (primeModNineClass X) - 1 / 6)) atTop := by
    filter_upwards [] with X
    exact abs_nonneg _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero' hz hBound hError

/-- The principal modulo36 term cancels in the actual witness's signed parity bias. -/
theorem tendsto_prime_mod_nine_class_bias :
    Tendsto (fun X : Nat => primeSubsetBias X (primeModNineClass X))
      atTop (nhds (0 : Real)) := by
  choose C hC using exists_primeCharacterSum_le_seven_eighths
  have hCpos : 0 < C := hC.1
  choose a19 ha19 using (show IsUnit (19 : ZMod 36) from by decide)
  have hError := (witness_error_ratio C 36 (by decide)).const_mul 2
  have hBound : Filter.Eventually (fun X : Nat =>
      abs (primeSubsetBias X (primeModNineClass X)) <=
        2 * (spectralWitnessError C 36 X /
          ((oddPrimeVertices X).card : Real))) atTop := by
    filter_upwards [] with X
    let E := spectralWitnessError C 36 X
    let U : Real := (((Nat.primesBelow (X + 1)).filter
      (fun p : Nat => IsUnit (p : ZMod 36))).card : Real) / ((36 : Nat).totient : Real)
    have hE : 0 <= E := by
      dsimp [E, spectralWitnessError]
      positivity
    have h1 := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      (Nat.primesBelow (X + 1)) (fun p : Nat => (p : ZMod 36))
      (1 : Units (ZMod 36)) E hE (fun chi hchi => hC.2 chi hchi X)
    have h19 := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      (Nat.primesBelow (X + 1)) (fun p : Nat => (p : ZMod 36))
      a19 E hE (fun chi hchi => hC.2 chi hchi X)
    rw [ha19] at h19
    change abs ((spectralWitnessResidueCount X 36 1 : Real) - U) <= E at h1
    change abs ((spectralWitnessResidueCount X 36 19 : Real) - U) <= E at h19
    have hDiff : abs ((spectralWitnessResidueCount X 36 1 : Real) -
        (spectralWitnessResidueCount X 36 19 : Real)) <= 2 * E := by
      calc
        _ = abs (((spectralWitnessResidueCount X 36 1 : Real) - U) +
            -((spectralWitnessResidueCount X 36 19 : Real) - U)) := by
          congr 1
          ring1
        _ <= abs ((spectralWitnessResidueCount X 36 1 : Real) - U) +
            abs (-((spectralWitnessResidueCount X 36 19 : Real) - U)) :=
          abs_add_le _ _
        _ <= 2 * E := by
          rw [abs_neg]
          linarith only [h1, h19]
    unfold primeSubsetBias
    rw [nine_bias_sum, abs_div, abs_of_nonneg
      (Nat.cast_nonneg (oddPrimeVertices X).card : (0 : Real) <= (oddPrimeVertices X).card)]
    have h := div_le_div_of_nonneg_right hDiff
      (Nat.cast_nonneg (oddPrimeVertices X).card : (0 : Real) <= (oddPrimeVertices X).card)
    simpa only [mul_div_assoc, E] using h
  have hz : Filter.Eventually (fun X : Nat =>
      0 <= abs (primeSubsetBias X (primeModNineClass X))) atTop := by
    filter_upwards [] with X
    exact abs_nonneg _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, sub_zero, mul_zero] using
    squeeze_zero' hz hBound (by simpa only [mul_zero] using hError)


/-- A candidate coefficient in the complete uniform signed spectral inequality. -/
def IsPrimeSquarefreeSpectralCoefficient (c : Real) : Prop :=
  forall eps : Real, 0 < eps ->
    Filter.Eventually (fun X : Nat => forall f : Nat -> Real,
      let A := artinPrimeSquareConstant
      let n := ((oddPrimeVertices X).card : Real)
      let a := (oddPrimeVertices X).sum f / n
      let b := (oddPrimeVertices X).sum (fun p : Nat => primeResidueSign p * f p) / n
      let e := (oddPrimeVertices X).sum (fun p : Nat => (f p) ^ 2) / n
      abs (Finset.kernelBilinear (oddPrimeVertices X)
        primeSquarefreeDifferenceKernel f f / n ^ 2 - A * (a ^ 2 - b ^ 2)) <=
          A * c * (e - a ^ 2 - b ^ 2) + eps * e) atTop

private theorem witness_spectral_inequality (c eps : Real)
    (hc : IsPrimeSquarefreeSpectralCoefficient c) (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat =>
      let a := primeSubsetDensity X (primeModNineClass X)
      let b := primeSubsetBias X (primeModNineClass X)
      artinPrimeSquareConstant * (a ^ 2 - b ^ 2) <=
        artinPrimeSquareConstant * c * (a - a ^ 2 - b ^ 2) + eps * a) atTop := by
  filter_upwards [hc eps heps] with X hS
  let S := oddPrimeVertices X
  let B := primeModNineClass X
  let n : Real := S.card
  let A := artinPrimeSquareConstant
  let f : Nat -> Real := fun p => if Membership.mem B p then 1 else 0
  have hB : B <= S := Finset.filter_subset _ _
  have hMean : S.sum f = (B.card : Real) := by
    calc
      _ = S.sum ((B : Set Nat).indicator (fun _ => (1 : Real))) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hb : Membership.mem B p <;> simp [f, Set.indicator, hb]
      _ = _ := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          Finset.sum_indicator_subset (fun _ => (1 : Real)) hB
  have hBias : S.sum (fun p : Nat => primeResidueSign p * f p) =
      B.sum primeResidueSign := by
    calc
      _ = S.sum ((B : Set Nat).indicator primeResidueSign) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hb : Membership.mem B p <;> simp [f, Set.indicator, hb]
      _ = _ := Finset.sum_indicator_subset primeResidueSign hB
  have hEnergy : S.sum (fun p : Nat => (f p) ^ 2) = (B.card : Real) := by
    calc
      _ = S.sum f := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hb : Membership.mem B p <;> simp [f, hb]
      _ = _ := hMean
  have hQ : Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f = 0 := by
    unfold Finset.kernelBilinear
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hpB : Membership.mem B p
    { by_cases hqB : Membership.mem B q
      { by_cases hpq : p = q
        { subst q
          simp [primeSquarefreeDifferenceKernel] }
        { have hIndependent := prime_mod_nine_class_independent X p hpB q hqB hpq
          simp [primeSquarefreeDifferenceKernel, hIndependent] } }
      { simp [f, hqB] } }
    { simp [f, hpB] }
  have h := hS f
  change abs (Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f / n ^ 2 -
      A * ((S.sum f / n) ^ 2 -
        (S.sum (fun p : Nat => primeResidueSign p * f p) / n) ^ 2)) <=
    A * c * (S.sum (fun p : Nat => (f p) ^ 2) / n - (S.sum f / n) ^ 2 -
      (S.sum (fun p : Nat => primeResidueSign p * f p) / n) ^ 2) +
        eps * (S.sum (fun p : Nat => (f p) ^ 2) / n) at h
  rw [hMean, hBias, hEnergy, hQ, zero_div, zero_sub, abs_neg] at h
  exact (le_abs_self _).trans h

private theorem spectral_coefficient_ge_fifth (c : Real)
    (hc : IsPrimeSquarefreeSpectralCoefficient c) : (1 / 5 : Real) <= c := by
  let A := artinPrimeSquareConstant
  have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 4)
    artinPrimeSquareConstant_bounds.1
  have ha := tendsto_prime_mod_nine_class_density
  have hb := tendsto_prime_mod_nine_class_bias
  have hLeft : Tendsto (fun X : Nat =>
      A * ((primeSubsetDensity X (primeModNineClass X)) ^ 2 -
        (primeSubsetBias X (primeModNineClass X)) ^ 2))
      atTop (nhds (A / 36)) := by
    have hValue : A * ((1 / 6 : Real) ^ 2 - (0 : Real) ^ 2) = A / 36 := by ring1
    simpa only [hValue] using ((ha.pow 2).sub (hb.pow 2)).const_mul A
  have hEstimate (eps : Real) (heps : 0 < eps) :
      A / 36 <= 5 * A * c / 36 + eps / 6 := by
    have hRight : Tendsto (fun X : Nat =>
        A * c * (primeSubsetDensity X (primeModNineClass X) -
          (primeSubsetDensity X (primeModNineClass X)) ^ 2 -
            (primeSubsetBias X (primeModNineClass X)) ^ 2) +
              eps * primeSubsetDensity X (primeModNineClass X))
        atTop (nhds (5 * A * c / 36 + eps / 6)) := by
      have hValue : A * c * ((1 / 6 : Real) - (1 / 6 : Real) ^ 2 - (0 : Real) ^ 2) +
          eps * (1 / 6 : Real) = 5 * A * c / 36 + eps / 6 := by ring1
      simpa only [hValue] using
        (((ha.sub (ha.pow 2)).sub (hb.pow 2)).const_mul (A * c)).add (ha.const_mul eps)
    exact le_of_tendsto_of_tendsto hLeft hRight
      (witness_spectral_inequality c eps hc heps)
  by_contra hNot
  have hGap : 0 < 1 - 5 * c := by linarith only [hNot]
  let eps := A * (1 - 5 * c) / 12
  have hEps : 0 < eps := by dsimp [eps]; positivity
  have hLimit := hEstimate eps hEps
  have hPositive := mul_pos hA hGap
  dsimp [eps] at hLimit
  nlinarith only [hLimit, hPositive]

/-- One fifth is the least possible coefficient, for the full uniform signed inequality. -/
theorem one_fifth_is_least_prime_squarefree_spectral_coefficient :
    IsLeast {c : Real | IsPrimeSquarefreeSpectralCoefficient c} (1 / 5 : Real) := by
  constructor
  { change IsPrimeSquarefreeSpectralCoefficient (1 / 5 : Real)
    intro eps heps
    filter_upwards [eventually_prime_squarefree_spectral_gap heps] with X hX
    intro f
    simpa only [div_eq_mul_inv, one_mul] using hX f }
  { intro c hc
    exact spectral_coefficient_ge_fifth c hc }

end PrimeFactorOscillations.QRH
