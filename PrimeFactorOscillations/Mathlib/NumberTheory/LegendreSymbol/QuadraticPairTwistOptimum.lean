/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistEnergy
/-!
# Exact optimal common-scale mixtures of quadratic-pair counts

Actual common scalings have only two count profiles, indexed by the
quadratic character, including the exceptional constants and repeated
shifts. For nonzero shifts and q > 5, every mean-one signed finite
mixture satisfies an exact second-moment minimum attained by positive
weights. Its energy is strictly larger than that of the flat admissible
law. The exceptional q = 3 and q = 5 cases are treated separately.

No Hasse bound, RH statement, or integer short-window estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistOptimum
attribute [local instance] Classical.propDecidable

def sumMoment (q epsilon : Real) : Real :=
  (q ^ 2 - 4 * q + 3 - 2 * (1 + epsilon) / q) / 4

def crossMoment (q s : Real) : Real := s * (q ^ 2 - 2 * q + 3) / (4 * q)

def diffMoment (q epsilon s : Real) : Real :=
  (q + s ^ 2 - (7 + s ^ 2 - 2 * epsilon) / q) / 4

def energy (q e f theta : Real) : Real :=
  4 * (sumMoment q (e * f) + 2 * crossMoment q (e + f) * theta +
    diffMoment q (e * f) (e + f) * theta ^ 2) /
      (q - 3 + (e + f) * theta) ^ 2

def optimalTheta (q e f : Real) : Real := (e + f) / (q + 3)

def minimumEnergy (q epsilon : Real) : Real :=
  if epsilon = 1 then (q + 1) ^ 2 / (q ^ 2 - 5) else (q - 1) / (q - 3)

def defectCoefficient (q epsilon : Real) : Real :=
  if epsilon = 1 then (q - 5) * (q - 1) * (q + 3) ^ 2 / (q * (q ^ 2 - 5))
    else (q ^ 2 - 9) / q

theorem mixture_denominator_pos (q e f theta : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (ht0 : -1 <= theta) (ht1 : theta <= 1) :
    0 < q - 3 + (e + f) * theta := by
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    nlinarith only [hq, ht0, ht1]

theorem moment_deficit_identity (q e f theta : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (ht0 : -1 <= theta) (ht1 : theta <= 1) :
    energy q e f theta =
      minimumEnergy q (e * f) +
        defectCoefficient q (e * f) * (theta - optimalTheta q e f) ^ 2 /
          (q - 3 + (e + f) * theta) ^ 2 := by
  have hq0 : Not (q = 0) := ne_of_gt (by linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  have hqp3 : Not (q + 3 = 0) := ne_of_gt (by linarith only [hq])
  have hq5 : Not (q ^ 2 - 5 = 0) :=
    ne_of_gt (by nlinarith only [sq_nonneg (q - 5), hq])
  have hD := ne_of_gt (mixture_denominator_pos q e f theta hq he hf ht0 ht1)
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [energy, sumMoment, crossMoment, diffMoment,
      minimumEnergy, optimalTheta, defectCoefficient] at * <;>
    field_simp [hq0, hq3, hqp3, hq5, hD] <;> ring

theorem defectCoefficient_pos (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    0 < defectCoefficient q (e * f) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hq5 : 0 < q ^ 2 - 5 := by nlinarith only [sq_nonneg (q - 5), hq]
  have hp : 0 < (q - 5) * (q - 1) * (q + 3) ^ 2 / (q * (q ^ 2 - 5)) :=
    div_pos
      (mul_pos (mul_pos (by linarith only [hq]) (by linarith only [hq]))
        (pow_pos (by linarith only [hq]) 2)) (mul_pos hq0 hq5)
  have hm : 0 < (q ^ 2 - 9) / q :=
    div_pos (by nlinarith only [sq_nonneg (q - 5), hq]) hq0
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [defectCoefficient] <;> assumption

theorem energy_lower (q e f theta : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (ht0 : -1 <= theta) (ht1 : theta <= 1) :
    minimumEnergy q (e * f) <= energy q e f theta := by
  rw [moment_deficit_identity q e f theta hq he hf ht0 ht1]
  apply le_add_of_nonneg_right
  apply div_nonneg
  . exact mul_nonneg (le_of_lt (defectCoefficient_pos q e f hq he hf)) (sq_nonneg _)
  . exact sq_nonneg _

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem monicQuadraticPairCount_square_scale
    (hF : Not (ringChar F = 2)) (s : F) (hs : Not (s = 0)) (c h : F) :
    monicQuadraticPairCount (s ^ 2 * c) (s ^ 2 * h) =
      monicQuadraticPairCount c h := by
  have hns (x : F) : Not (IsSquare (s ^ 2 * x)) <-> Not (IsSquare x) := by
    simp only [<- quadraticChar_neg_one_iff_not_isSquare,
      map_mul, map_pow, quadraticChar_sq_one hs, one_mul]
  let eqv : Equiv F F :=
    { toFun := fun b => s * b
      invFun := fun b => b / s
      left_inv := by intro b; field_simp [hs]
      right_inv := by intro b; field_simp [hs] }
  have hdisc1 (b : F) :
      (eqv b) ^ 2 - 4 * (s ^ 2 * c) = s ^ 2 * (b ^ 2 - 4 * c) := by
    change (s * b) ^ 2 - 4 * (s ^ 2 * c) = _
    ring
  have hdisc2 (b : F) :
      (eqv b) ^ 2 - 4 * (s ^ 2 * c + s ^ 2 * h) =
        s ^ 2 * (b ^ 2 - 4 * (c + h)) := by
    change (s * b) ^ 2 - 4 * (s ^ 2 * c + s ^ 2 * h) = _
    ring
  unfold monicQuadraticPairCount
  calc
    _ = Finset.univ.sum (fun b : F =>
        if Irreducible (monicQuadratic (eqv b) (s ^ 2 * c)) /\
          Irreducible (monicQuadratic (eqv b) (s ^ 2 * c + s ^ 2 * h))
          then (1 : Int) else 0) :=
      (Equiv.sum_comp eqv _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [monicQuadratic_irreducible_iff_nonsquare hF, hdisc1, hdisc2, hns]

theorem monicQuadraticPairCount_eq_of_character
    (hF : Not (ringChar F = 2)) (t u : F)
    (ht : Not (t = 0)) (hu : Not (u = 0))
    (hchi : (quadraticChar F) t = (quadraticChar F) u) (c h : F) :
    monicQuadraticPairCount (t * c) (t * h) =
      monicQuadraticPairCount (u * c) (u * h) := by
  have htu : Not (t * u = 0) := mul_ne_zero ht hu
  have hp : (quadraticChar F) (t * u) = 1 := by
    rw [map_mul, hchi]
    nlinarith only [quadraticChar_sq_one hu]
  choose s hs using (quadraticChar_one_iff_isSquare htu).mp hp
  have hsq : s ^ 2 = t * u := by simpa only [pow_two] using hs.symm
  have hs0 : Not (s = 0) := by
    intro hz
    apply htu
    rw [<- hsq, hz]
    simp
  have hscale : (s / u) ^ 2 * u = t := by
    calc
      _ = s ^ 2 / u := by field_simp [hu] <;> ring
      _ = (t * u) / u := by rw [hsq]
      _ = t := by field_simp [hu]
  have hi := monicQuadraticPairCount_square_scale hF (s / u)
    (div_ne_zero hs0 hu) (u * c) (u * h)
  simpa only [<- mul_assoc, hscale] using hi

theorem monicQuadraticPairCount_two_classes
    (hF : Not (ringChar F = 2)) (t u : F)
    (ht : Not (t = 0)) (hu : Not (u = 0)) (hchi : (quadraticChar F) u = -1)
    (c h : F) :
    monicQuadraticPairCount (t * c) (t * h) =
      if (quadraticChar F) t = 1 then monicQuadraticPairCount c h
        else monicQuadraticPairCount (u * c) (u * h) := by
  by_cases hp : (quadraticChar F) t = 1
  . simp only [ite_eq_left hp]
    have hi := monicQuadraticPairCount_eq_of_character hF t (1 : F)
      ht one_ne_zero (by simpa using hp) c h
    simpa only [one_mul] using hi
  . have hn : (quadraticChar F) t = -1 := by
      rcases QuadraticPairEuler.quadraticChar_real_signs t ht with he | he
      . exact False.elim (hp (by exact_mod_cast he))
      . exact_mod_cast he
    simp only [ite_eq_right hp]
    exact monicQuadraticPairCount_eq_of_character hF t u ht hu (by rw [hn, hchi]) c h

def signE (h : F) : Real := ((quadraticChar F) h : Real)
def signF (h : F) : Real := ((quadraticChar F) (-h) : Real)
def countPlus (c h t : F) : Real :=
  (monicQuadraticPairCount c h : Real) + (monicQuadraticPairCount (t * c) (t * h) : Real)
def countDiff (c h t : F) : Real :=
  (monicQuadraticPairCount c h : Real) - (monicQuadraticPairCount (t * c) (t * h) : Real)
def rawSquarePolynomial (q s : Real) : Real :=
  (q - 3 + s) * (q ^ 2 + s * q + 3 - s)

theorem sign_product (h : F) (hh : Not (h = 0)) :
    ((quadraticChar F) (-1) : Real) = signE h * signF h := by
  have hp : signF h * signE h = ((quadraticChar F) (-1) : Real) := by
    dsimp [signE, signF]
    exact_mod_cast quadraticChar_shift_product h hh
  rw [<- hp, mul_comm]

theorem base_square_sum (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    16 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real) ^ 2) =
      rawSquarePolynomial (Fintype.card F : Real) (signE h + signF h) := by
  have hi :
      16 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real) ^ 2) =
        ((Fintype.card F : Real) - (quadraticPairOffset h : Real)) *
          ((Fintype.card F : Real) ^ 2 +
            (3 - (quadraticPairOffset h : Real)) * (Fintype.card F : Real) +
              (quadraticPairOffset h : Real)) := by
    exact_mod_cast sum_monicQuadraticPairCount_square hF h hh
  have hoff : (quadraticPairOffset h : Real) = 3 - signE h - signF h := by
    norm_num [quadraticPairOffset, signE, signF]
  rw [hoff] at hi
  unfold rawSquarePolynomial
  convert hi using 1 <;> ring

theorem twist_square_sum (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    16 * (Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount (t * c) (t * h) : Real) ^ 2) =
      rawSquarePolynomial (Fintype.card F : Real) (-(signE h + signF h)) := by
  let eqv : Equiv F F :=
    { toFun := fun c => t * c
      invFun := fun c => c / t
      left_inv := by intro c; field_simp [ht]
      right_inv := by intro c; field_simp [ht] }
  have hreindex :
      (Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount (t * c) (t * h) : Real) ^ 2) =
      Finset.univ.sum (fun c : F =>
        (monicQuadraticPairCount c (t * h) : Real) ^ 2) :=
    Equiv.sum_comp eqv (fun c : F => (monicQuadraticPairCount c (t * h) : Real) ^ 2)
  have he : signE (t * h) = -signE h := by
    simp only [signE, map_mul, hchi, neg_one_mul, Int.cast_neg]
  have hf : signF (t * h) = -signF h := by
    have heq : -(t * h) = t * (-h) := by ring
    simp only [signF, heq, map_mul, hchi, neg_one_mul, Int.cast_neg]
  rw [hreindex, base_square_sum hF (t * h) (mul_ne_zero ht hh), he, hf]
  congr 1
  ring

theorem sum_countPlus_square (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    4 * (Finset.univ.sum fun c : F => (countPlus c h t) ^ 2) =
      (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) ^ 2 +
        2 * (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) -
          2 * (1 + signE h * signF h) := by
  have hi :
      (Finset.univ.sum fun c : F => (traceFreePairNumerator c h : Real) ^ 2) =
        (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) ^ 2 +
          2 * (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) -
            2 * (1 + ((quadraticChar F) (-1) : Real)) := by
    exact_mod_cast sum_traceFreePairNumerator_square hF h hh
  have hp (c : F) : (traceFreePairNumerator c h : Real) = 2 * countPlus c h t := by
    dsimp [countPlus]
    exact_mod_cast traceFreePairNumerator_eq_twist_counts hF c h t hh ht hchi
  have hs (c : F) : (2 * countPlus c h t) ^ 2 = 4 * (countPlus c h t) ^ 2 := by ring
  simp_rw [hp, hs] at hi
  rw [<- Finset.mul_sum, sign_product h hh] at hi
  exact hi

theorem sum_countPlus_countDiff (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    4 * (Finset.univ.sum fun c : F => countPlus c h t * countDiff c h t) =
      (signE h + signF h) *
        ((Fintype.card F : Real) ^ 2 - 2 * (Fintype.card F : Real) + 3) := by
  have h1 := base_square_sum hF h hh
  have h2 := twist_square_sum hF h t hh ht hchi
  have hp (c : F) : countPlus c h t * countDiff c h t =
      (monicQuadraticPairCount c h : Real) ^ 2 -
        (monicQuadraticPairCount (t * c) (t * h) : Real) ^ 2 := by
    dsimp [countPlus, countDiff]
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib]
  unfold rawSquarePolynomial at h1 h2
  nlinarith only [h1, h2]

theorem sum_countDiff_square (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    4 * (Finset.univ.sum fun c : F => (countDiff c h t) ^ 2) =
      (Fintype.card F : Real) ^ 2 +
        (Fintype.card F : Real) * (signE h + signF h) ^ 2 -
          (7 + (signE h + signF h) ^ 2 - 2 * (signE h * signF h)) := by
  have h1 := base_square_sum hF h hh
  have h2 := twist_square_sum hF h t hh ht hchi
  have hS := sum_countPlus_square hF h t hh ht hchi
  have hp (c : F) : (countDiff c h t) ^ 2 =
      2 * (monicQuadraticPairCount c h : Real) ^ 2 +
        2 * (monicQuadraticPairCount (t * c) (t * h) : Real) ^ 2 -
          (countPlus c h t) ^ 2 := by
    dsimp [countPlus, countDiff]
    ring
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]
  unfold rawSquarePolynomial at h1 h2
  nlinarith only [h1, h2, hS]

def spanEnergy (q e f alpha beta : Real) : Real :=
  alpha ^ 2 * sumMoment q (e * f) +
    2 * alpha * beta * crossMoment q (e + f) +
      beta ^ 2 * diffMoment q (e * f) (e + f)

def optimalAlpha (q e f : Real) : Real :=
  2 * (q + 3) / (q ^ 2 - 9 + (e + f) ^ 2)

def optimalBeta (q e f : Real) : Real :=
  2 * (e + f) / (q ^ 2 - 9 + (e + f) ^ 2)

def spanDefectCoefficient (q epsilon : Real) : Real :=
  if epsilon = 1 then (q ^ 2 - 5) * (q - 5) * (q - 1) / (4 * q * (q - 3) ^ 2)
    else (q ^ 2 - 9) / (4 * q)

theorem optimalBeta_eq_piecewise (q e f : Real)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    optimalBeta q e f =
      if e * f = 1 then 2 * (e + f) / (q ^ 2 - 5) else 0 := by
  have he2 : e ^ 2 = 1 := by rcases he with he | he <;> rw [he] <;> norm_num
  have hf2 : f ^ 2 = 1 := by rcases hf with hf | hf <;> rw [hf] <;> norm_num
  by_cases hp : e * f = 1
  . simp only [ite_eq_left hp]
    have hs : (e + f) ^ 2 = 4 := by nlinarith only [he2, hf2, hp]
    unfold optimalBeta
    congr 1
    nlinarith only [hs]
  . simp only [ite_eq_right hp]
    have hs : e + f = 0 := by
      rcases he with he | he <;> rcases hf with hf | hf <;>
        subst e <;> subst f <;> norm_num at *
    simp [optimalBeta, hs]

theorem span_deficit_identity (q e f alpha beta : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hmean : alpha * (q - 3) + beta * (e + f) = 2) :
    spanEnergy q e f alpha beta =
      minimumEnergy q (e * f) +
        spanDefectCoefficient q (e * f) * (beta - optimalBeta q e f) ^ 2 := by
  have hq0 : Not (q = 0) := ne_of_gt (by linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  have hq5 : Not (q ^ 2 - 5 = 0) :=
    ne_of_gt (by nlinarith only [sq_nonneg (q - 5), hq])
  have ha : alpha = (2 - beta * (e + f)) / (q - 3) := by
    field_simp [hq3]
    nlinarith only [hmean]
  rw [ha, optimalBeta_eq_piecewise q e f he hf]
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [spanEnergy, sumMoment, crossMoment, diffMoment,
      minimumEnergy, spanDefectCoefficient] <;>
    field_simp [hq0, hq3, hq5] <;> ring

theorem spanDefectCoefficient_pos (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    0 < spanDefectCoefficient q (e * f) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hq5 : 0 < q ^ 2 - 5 := by nlinarith only [sq_nonneg (q - 5), hq]
  have hp : 0 < (q ^ 2 - 5) * (q - 5) * (q - 1) / (4 * q * (q - 3) ^ 2) :=
    div_pos
      (mul_pos (mul_pos hq5 (by linarith only [hq])) (by linarith only [hq]))
      (mul_pos (mul_pos (by norm_num) hq0) (pow_pos (by linarith only [hq]) 2))
  have hm : 0 < (q ^ 2 - 9) / (4 * q) :=
    div_pos (by nlinarith only [sq_nonneg (q - 5), hq]) (mul_pos (by norm_num) hq0)
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [spanDefectCoefficient] <;> assumption

theorem optimal_coefficients_mean (q e f : Real) (hq : 5 < q) :
    optimalAlpha q e f * (q - 3) + optimalBeta q e f * (e + f) = 2 := by
  have hd : Not (q ^ 2 - 9 + (e + f) ^ 2 = 0) :=
    ne_of_gt (by nlinarith only [sq_nonneg (q - 5), sq_nonneg (e + f), hq])
  unfold optimalAlpha optimalBeta
  field_simp [hd]
  <;> ring

theorem span_energy_minimum (q e f alpha beta : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hmean : alpha * (q - 3) + beta * (e + f) = 2) :
    minimumEnergy q (e * f) <= spanEnergy q e f alpha beta /\
      (spanEnergy q e f alpha beta = minimumEnergy q (e * f) <->
        beta = optimalBeta q e f) := by
  have hi := span_deficit_identity q e f alpha beta hq he hf hmean
  have hp := spanDefectCoefficient_pos q e f hq he hf
  constructor
  . have hnn := mul_nonneg (le_of_lt hp) (sq_nonneg (beta - optimalBeta q e f))
    linarith only [hi, hnn]
  . constructor
    . intro heq
      have hz : spanDefectCoefficient q (e * f) * (beta - optimalBeta q e f) ^ 2 = 0 := by
        linarith only [hi, heq]
      have hs := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    . intro hb
      rw [hb, sub_self, zero_pow (by decide : Not (2 = 0)), mul_zero, add_zero] at hi
      simpa only [hb] using hi

theorem rawCount_nonneg (c h : F) : 0 <= monicQuadraticPairCount c h := by
  unfold monicQuadraticPairCount
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> norm_num

theorem card_five_sign_sum (hF : Not (ringChar F = 2))
    (hcard : Fintype.card F = 5) (h : F) (hh : Not (h = 0)) :
    (quadraticChar F) h + (quadraticChar F) (-h) = 2 \/
      (quadraticChar F) h + (quadraticChar F) (-h) = -2 := by
  have hsum := sum_monicQuadraticPairCount_eq hF h hh
  rw [hcard] at hsum
  norm_num at hsum
  have hbad : Not ((quadraticChar F) h + (quadraticChar F) (-h) = 0) := by
    intro hz
    norm_num at hz
    have hi : 4 * (Finset.univ.sum fun c : F => monicQuadraticPairCount c h) = 10 := by
      nlinarith only [hsum, hz]
    have hm := congrArg (fun z : Int => z % 4) hi
    norm_num [Int.mul_emod] at hm
  rcases QuadraticPairEuler.quadraticChar_real_signs h hh with he | he <;>
    rcases QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh) with hf | hf
  . left
    have he' : (quadraticChar F) h = 1 := by exact_mod_cast he
    have hf' : (quadraticChar F) (-h) = 1 := by exact_mod_cast hf
    rw [he', hf']
    norm_num
  . have he' : (quadraticChar F) h = 1 := by exact_mod_cast he
    have hf' : (quadraticChar F) (-h) = -1 := by exact_mod_cast hf
    exact False.elim (hbad (by rw [he', hf']; norm_num))
  . have he' : (quadraticChar F) h = -1 := by exact_mod_cast he
    have hf' : (quadraticChar F) (-h) = 1 := by exact_mod_cast hf
    exact False.elim (hbad (by rw [he', hf']; norm_num))
  . right
    have he' : (quadraticChar F) h = -1 := by exact_mod_cast he
    have hf' : (quadraticChar F) (-h) = -1 := by exact_mod_cast hf
    rw [he', hf']
    norm_num

theorem card_three_count_zero (hF : Not (ringChar F = 2))
    (hcard : Fintype.card F = 3) (c h : F) (hh : Not (h = 0)) :
    monicQuadraticPairCount c h = 0 := by
  choose t ht using exists_nonsquare_twist (F := F) hF
  have hsum := sum_twistTaggedPairCount hF h t hh ht.1 ht.2
  rw [hcard] at hsum
  norm_num at hsum
  have hs : (Finset.univ.sum fun z : F =>
      monicQuadraticPairCount z h + monicQuadraticPairCount (t * z) (t * h)) = 0 := by
    nlinarith only [hsum]
  have hp := Finset.single_le_sum
    (fun z (_ : Membership.mem (Finset.univ : Finset F) z) =>
      add_nonneg (rawCount_nonneg z h) (rawCount_nonneg (t * z) (t * h)))
    (Finset.mem_univ c)
  rw [hs] at hp
  have hfirst := rawCount_nonneg c h
  have hsecond := rawCount_nonneg (t * c) (t * h)
  linarith only [hp, hfirst, hsecond]

def linearProfile (c h t : F) (alpha beta : Real) : Real :=
  alpha * countPlus c h t + beta * countDiff c h t

theorem sum_countPlus (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    2 * (Finset.univ.sum fun c : F => countPlus c h t) =
      (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) := by
  dsimp [countPlus]
  exact_mod_cast sum_twistTaggedPairCount hF h t hh ht hchi

theorem sum_countDiff (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    2 * (Finset.univ.sum fun c : F => countDiff c h t) =
      (Fintype.card F : Real) * (signE h + signF h) := by
  have hplus := sum_countPlus hF h t hh ht hchi
  have hbase :
      4 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real)) =
        (Fintype.card F : Real) *
          ((Fintype.card F : Real) - 3 + signE h + signF h) := by
    dsimp [signE, signF]
    exact_mod_cast sum_monicQuadraticPairCount_eq hF h hh
  have hp (c : F) : countDiff c h t =
      2 * (monicQuadraticPairCount c h : Real) - countPlus c h t := by
    dsimp [countPlus, countDiff]
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
  linarith only [hbase, hplus]

theorem linearProfile_mean (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (alpha beta : Real) :
    (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => linearProfile c h t alpha beta) =
      (alpha * ((Fintype.card F : Real) - 3) +
        beta * (signE h + signF h)) / 2 := by
  have hq0 : Not ((Fintype.card F : Real) = 0) := by
    exact_mod_cast (show Not (Fintype.card F = 0) from Fintype.card_ne_zero)
  have hs : (Finset.univ.sum fun c : F => countPlus c h t) =
      (Fintype.card F : Real) * ((Fintype.card F : Real) - 3) / 2 := by
    linarith only [sum_countPlus hF h t hh ht hchi]
  have hd : (Finset.univ.sum fun c : F => countDiff c h t) =
      (Fintype.card F : Real) * (signE h + signF h) / 2 := by
    linarith only [sum_countDiff hF h t hh ht hchi]
  unfold linearProfile
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum, hs, hd]
  field_simp [hq0]
  <;> ring

theorem linearProfile_energy (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (alpha beta : Real) :
    (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (linearProfile c h t alpha beta) ^ 2) =
      spanEnergy (Fintype.card F : Real) (signE h) (signF h) alpha beta := by
  have hq0 : Not ((Fintype.card F : Real) = 0) := by
    exact_mod_cast (show Not (Fintype.card F = 0) from Fintype.card_ne_zero)
  have hs : (Finset.univ.sum fun c : F => (countPlus c h t) ^ 2) =
      (Fintype.card F : Real) *
        sumMoment (Fintype.card F : Real) (signE h * signF h) := by
    unfold sumMoment
    field_simp [hq0]
    nlinarith only [sum_countPlus_square hF h t hh ht hchi]
  have hc : (Finset.univ.sum fun c : F => countPlus c h t * countDiff c h t) =
      (Fintype.card F : Real) *
        crossMoment (Fintype.card F : Real) (signE h + signF h) := by
    unfold crossMoment
    field_simp [hq0]
    nlinarith only [sum_countPlus_countDiff hF h t hh ht hchi]
  have hd : (Finset.univ.sum fun c : F => (countDiff c h t) ^ 2) =
      (Fintype.card F : Real) *
        diffMoment (Fintype.card F : Real) (signE h * signF h) (signE h + signF h) := by
    unfold diffMoment
    field_simp [hq0]
    nlinarith only [sum_countDiff_square hF h t hh ht hchi]
  have hp (c : F) : (linearProfile c h t alpha beta) ^ 2 =
      alpha ^ 2 * (countPlus c h t) ^ 2 +
        (2 * alpha * beta) * (countPlus c h t * countDiff c h t) +
          beta ^ 2 * (countDiff c h t) ^ 2 := by
    unfold linearProfile
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
  rw [hs, hc, hd]
  unfold spanEnergy
  field_simp [hq0]
  <;> ring

theorem linearProfile_energy_minimum (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hq : 5 < (Fintype.card F : Real)) (alpha beta : Real)
    (hmean : (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => linearProfile c h t alpha beta) = 1) :
    minimumEnergy (Fintype.card F : Real) (signE h * signF h) <=
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (linearProfile c h t alpha beta) ^ 2) /\
    ((1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (linearProfile c h t alpha beta) ^ 2) =
      minimumEnergy (Fintype.card F : Real) (signE h * signF h) <->
      beta = optimalBeta (Fintype.card F : Real) (signE h) (signF h)) := by
  rw [linearProfile_mean hF h t hh ht hchi alpha beta] at hmean
  have hm : alpha * ((Fintype.card F : Real) - 3) +
      beta * (signE h + signF h) = 2 := by linarith only [hmean]
  rw [linearProfile_energy hF h t hh ht hchi alpha beta]
  exact span_energy_minimum _ _ _ alpha beta hq
    (QuadraticPairEuler.quadraticChar_real_signs h hh)
    (QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)) hm

theorem minimumEnergy_flat_gap (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    minimumEnergy q (e * f) - q / (q - 2) =
      if e * f = 1 then 2 * (q - 1) / ((q ^ 2 - 5) * (q - 2))
        else 2 / ((q - 3) * (q - 2)) := by
  have h2 : Not (q - 2 = 0) := ne_of_gt (by linarith only [hq])
  have h3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  have h5 : Not (q ^ 2 - 5 = 0) :=
    ne_of_gt (by nlinarith only [sq_nonneg (q - 5), hq])
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [minimumEnergy] <;> field_simp [h2,h3,h5] <;> ring

theorem minimumEnergy_strict_flat (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    q / (q - 2) < minimumEnergy q (e * f) := by
  have hi := minimumEnergy_flat_gap q e f hq he hf
  have h2 : 0 < q - 2 := by linarith only [hq]
  have h3 : 0 < q - 3 := by linarith only [hq]
  have h5 : 0 < q ^ 2 - 5 := by nlinarith only [sq_nonneg (q - 5), hq]
  have hp : 0 < 2 * (q - 1) / ((q ^ 2 - 5) * (q - 2)) :=
    div_pos (mul_pos (by norm_num) (by linarith only [hq])) (mul_pos h5 h2)
  have hm : 0 < 2 / ((q - 3) * (q - 2)) := div_pos (by norm_num) (mul_pos h3 h2)
  split_ifs at hi <;> linarith only [hi,hp,hm]


theorem optimal_raw_coefficients_pos (q e f : Real) (hq : 5 < q)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1) :
    0 < optimalAlpha q e f + optimalBeta q e f /\
      0 < optimalAlpha q e f - optimalBeta q e f := by
  have hb : -2 <= e + f /\ e + f <= 2 := by
    rcases he with he | he <;> rcases hf with hf | hf <;>
      subst e <;> subst f <;> norm_num
  have hd : 0 < q ^ 2 - 9 + (e + f) ^ 2 := by
    nlinarith only [sq_nonneg (q - 5), sq_nonneg (e + f), hq]
  unfold optimalAlpha optimalBeta
  constructor
  . rw [<- add_div]
    exact div_pos (by linarith only [hq, hb.1]) hd
  . rw [<- sub_div]
    exact div_pos (by linarith only [hq, hb.2]) hd

def optimalProfile (c h t : F) : Real :=
  linearProfile c h t (optimalAlpha (Fintype.card F : Real) (signE h) (signF h))
    (optimalBeta (Fintype.card F : Real) (signE h) (signF h))

theorem optimalProfile_law (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hq : 5 < (Fintype.card F : Real)) :
    ((1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => optimalProfile c h t) = 1) /\
    ((1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (optimalProfile c h t) ^ 2) =
        minimumEnergy (Fintype.card F : Real) (signE h * signF h)) /\
    (forall c : F, 0 <= optimalProfile c h t) := by
  have he := QuadraticPairEuler.quadraticChar_real_signs h hh
  have hf := QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)
  have hm := optimal_coefficients_mean (Fintype.card F : Real) (signE h) (signF h) hq
  constructor
  . unfold optimalProfile
    rw [linearProfile_mean hF h t hh ht hchi, hm]
    norm_num
  . constructor
    . unfold optimalProfile
      rw [linearProfile_energy hF h t hh ht hchi]
      exact ((span_energy_minimum _ _ _ _ _ hq he hf hm).2).mpr rfl
    . intro c
      have hp := optimal_raw_coefficients_pos (Fintype.card F : Real) (signE h) (signF h) hq he hf
      have h1 : 0 <= (monicQuadraticPairCount c h : Real) := by
        exact_mod_cast rawCount_nonneg c h
      have h2 : 0 <= (monicQuadraticPairCount (t * c) (t * h) : Real) := by
        exact_mod_cast rawCount_nonneg (t * c) (t * h)
      unfold optimalProfile linearProfile countPlus countDiff
      nlinarith only [mul_nonneg (le_of_lt hp.1) h1, mul_nonneg (le_of_lt hp.2) h2]


theorem scaled_count_linearProfile (hF : Not (ringChar F = 2)) (h u t c : F)
    (hu : Not (u = 0)) (hchi : (quadraticChar F) u = -1)
    (ht : Not (t = 0)) :
    (monicQuadraticPairCount (t * c) (t * h) : Real) =
      linearProfile c h u (1 / 2) (((quadraticChar F) t : Real) / 2) := by
  have hi := monicQuadraticPairCount_two_classes hF t u ht hu hchi c h
  by_cases hp : (quadraticChar F) t = 1
  . rw [ite_eq_left hp] at hi
    rw [hi]
    unfold linearProfile countPlus countDiff
    rw [hp]
    norm_num
    <;> ring
  . have hn : (quadraticChar F) t = -1 := by
      rcases QuadraticPairEuler.quadraticChar_real_signs t ht with he | he
      . exact False.elim (hp (by exact_mod_cast he))
      . exact_mod_cast he
    rw [ite_eq_right hp] at hi
    rw [hi]
    unfold linearProfile countPlus countDiff
    rw [hn]
    norm_num
    <;> ring

def scalingMixture {J : Type*} [Fintype J]
    (c h : F) (scale : J -> F) (weight : J -> Real) : Real :=
  Finset.univ.sum fun i : J =>
    weight i * (monicQuadraticPairCount (scale i * c) (scale i * h) : Real)

theorem scalingMixture_eq_span {J : Type*} [Fintype J]
    (hF : Not (ringChar F = 2)) (h u c : F)
    (hu : Not (u = 0)) (hchi : (quadraticChar F) u = -1)
    (scale : J -> F) (ht : forall i, Not (scale i = 0)) (weight : J -> Real) :
    scalingMixture c h scale weight =
      linearProfile c h u
        (Finset.univ.sum fun i : J => weight i / 2)
        (Finset.univ.sum fun i : J => weight i * ((quadraticChar F) (scale i) : Real) / 2) := by
  have hp (i : J) :
      weight i * (monicQuadraticPairCount (scale i * c) (scale i * h) : Real) =
        (weight i / 2) * countPlus c h u +
          (weight i * ((quadraticChar F) (scale i) : Real) / 2) * countDiff c h u := by
    rw [scaled_count_linearProfile hF h u (scale i) c hu hchi (ht i)]
    unfold linearProfile
    ring
  unfold scalingMixture
  simp_rw [hp]
  rw [Finset.sum_add_distrib, <- Finset.sum_mul, <- Finset.sum_mul]
  rfl

theorem scalingMixture_energy_minimum {J : Type*} [Fintype J]
    (hF : Not (ringChar F = 2)) (h u : F)
    (hh : Not (h = 0)) (hu : Not (u = 0)) (hchi : (quadraticChar F) u = -1)
    (hq : 5 < (Fintype.card F : Real))
    (scale : J -> F) (ht : forall i, Not (scale i = 0)) (weight : J -> Real)
    (hmean : (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => scalingMixture c h scale weight) = 1) :
    minimumEnergy (Fintype.card F : Real) (signE h * signF h) <=
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (scalingMixture c h scale weight) ^ 2) := by
  have hp (c : F) := scalingMixture_eq_span hF h u c hu hchi scale ht weight
  simp_rw [hp] at hmean
  simp_rw [hp]
  exact (linearProfile_energy_minimum hF h u hh hu hchi hq _ _ hmean).1



theorem span_energy_five (e f alpha beta : Real)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hs : e + f = 2 \/ e + f = -2)
    (hmean : alpha * (5 - 3) + beta * (e + f) = 2) :
    spanEnergy 5 e f alpha beta = 9 / 5 := by
  rcases he with he | he <;> rcases hf with hf | hf <;> subst e <;> subst f <;>
    norm_num [spanEnergy, sumMoment, crossMoment, diffMoment] at *
  all_goals
    first
    | have ha : alpha = 1 - beta := by linarith only [hmean]
      rw [ha]
      ring
    | have ha : alpha = 1 + beta := by linarith only [hmean]
      rw [ha]
      ring

theorem card_five_linearProfile_energy (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hcard : Fintype.card F = 5) (alpha beta : Real)
    (hmean : (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => linearProfile c h t alpha beta) = 1) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (linearProfile c h t alpha beta) ^ 2) = 9 / 5 := by
  have hm := linearProfile_mean hF h t hh ht hchi alpha beta
  rw [hmean, hcard] at hm
  norm_num only [Nat.cast_ofNat] at hm
  have hs : signE h + signF h = 2 \/ signE h + signF h = -2 :=
by
      dsimp [signE, signF]
      exact_mod_cast card_five_sign_sum hF hcard h hh
  rw [linearProfile_energy hF h t hh ht hchi alpha beta, hcard]
  norm_num only [Nat.cast_ofNat]
  exact span_energy_five _ _ alpha beta
    (QuadraticPairEuler.quadraticChar_real_signs h hh)
    (QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)) hs
    (by linarith only [hm])



theorem scalingMixture_strict_flat {J : Type*} [Fintype J]
    (hF : Not (ringChar F = 2)) (h u : F)
    (hh : Not (h = 0)) (hu : Not (u = 0)) (hchi : (quadraticChar F) u = -1)
    (hq : 5 < (Fintype.card F : Real))
    (scale : J -> F) (ht : forall i, Not (scale i = 0)) (weight : J -> Real)
    (hmean : (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => scalingMixture c h scale weight) = 1) :
    (Fintype.card F : Real) / ((Fintype.card F : Real) - 2) <
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (scalingMixture c h scale weight) ^ 2) := by
  exact lt_of_lt_of_le
    (minimumEnergy_strict_flat _ _ _ hq
      (QuadraticPairEuler.quadraticChar_real_signs h hh)
      (QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)))
    (scalingMixture_energy_minimum hF h u hh hu hchi hq scale ht weight hmean)

end FiniteField.QuadraticPairTwistOptimum
