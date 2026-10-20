/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleWavePair

/-!
# PowerSampleEulerCorrection

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.ProbePowerGauss

def fourthCoprimeKernel (r u C omega v a b : Complex) : Complex :=
  1 + r * (1 - (1 - u) * (1 + C * v) / (1 - v ^ 2)) +
    (1 + C * omega * v) / (1 - v ^ 2) * (a - b)

def fourthEulerCorrection (r u C omega v a b : Complex) : Complex :=
  fourthCoprimeKernel r u C omega v a b * (1 - a) / (1 - b)

def fourthEulerRemainder (r u C omega v a b : Complex) : Complex :=
  r * (u + C * v * (u - 1) - v ^ 2) +
    (C * omega * v + v ^ 2) * (a - b)

def fourthEulerAllowance (r u v a b : Complex) : Real :=
  norm r * (norm u + norm v * (norm u + 1) + norm v ^ 2) +
    (norm v + norm v ^ 2) * (norm a + norm b)

theorem fourthEulerCorrection_identity (r u C omega v a b : Complex)
    (hv : Not (1 - v ^ 2 = 0)) (hb : Not (1 - b = 0)) :
    fourthEulerCorrection r u C omega v a b - 1 =
      (-a ^ 2 + a * b +
        (1 - a) * (fourthEulerRemainder r u C omega v a b / (1 - v ^ 2))) /
      (1 - b) := by
  unfold fourthEulerCorrection fourthCoprimeKernel fourthEulerRemainder
  field_simp
  <;> ring

theorem fourthEulerRemainder_norm (r u C omega v a b : Complex)
    (hC : norm C <= 1) (ho : norm omega <= 1) :
    norm (fourthEulerRemainder r u C omega v a b) <=
      fourthEulerAllowance r u v a b := by
  have hCv : norm (C * v) <= norm v := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hC
  have hCov : norm (C * omega * v) <= norm v := by
    rw [norm_mul, norm_mul]
    have he : norm C * norm omega <= 1 := by
      nlinarith [norm_nonneg C, norm_nonneg omega]
    exact mul_le_of_le_one_left (norm_nonneg _) he
  have h1 : norm (u + C * v * (u - 1) - v ^ 2) <=
      norm u + norm v * (norm u + 1) + norm v ^ 2 := by
    calc
      _ <= norm (u + C * v * (u - 1)) + norm (v ^ 2) := norm_sub_le _ _
      _ <= norm u + norm (C * v * (u - 1)) + norm (v ^ 2) := by
        linarith [norm_add_le u (C * v * (u - 1))]
      _ <= _ := by
        rw [norm_mul, norm_pow]
        have he : norm (u - 1) <= norm u + 1 := by
          simpa only [norm_one] using norm_sub_le u (1 : Complex)
        nlinarith [norm_nonneg (u - 1), norm_nonneg v, norm_nonneg u,
          mul_le_mul hCv he (norm_nonneg (u - 1)) (norm_nonneg v)]
  have h2 : norm (C * omega * v + v ^ 2) <= norm v + norm v ^ 2 := by
    exact (norm_add_le _ _).trans (by rw [norm_pow]; linarith)
  have h3 : norm (a - b) <= norm a + norm b := norm_sub_le _ _
  unfold fourthEulerRemainder fourthEulerAllowance
  calc
    _ <= norm (r * (u + C * v * (u - 1) - v ^ 2)) +
        norm ((C * omega * v + v ^ 2) * (a - b)) := norm_add_le _ _
    _ <= _ := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
        (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))

theorem fourthEulerCorrection_norm (r u C omega v a b : Complex)
    (hC : norm C <= 1) (ho : norm omega <= 1)
    (ha : norm a <= 1/2) (hb : norm b <= 1/2) (hv : norm v <= 1/2) :
    norm (fourthEulerCorrection r u C omega v a b - 1) <=
      8 * (norm a ^ 2 + norm a * norm b + fourthEulerAllowance r u v a b) := by
  let N := fourthEulerAllowance r u v a b
  have hN0 : 0 <= N := by unfold N fourthEulerAllowance; positivity
  have hN := fourthEulerRemainder_norm r u C omega v a b hC ho
  have hDlow : 1/2 <= norm ((1 : Complex) - v ^ 2) := by
    have he := norm_sub_norm_le (1 : Complex) (v ^ 2)
    rw [norm_one, norm_pow] at he
    nlinarith [norm_nonneg v]
  have hblow : 1/2 <= norm ((1 : Complex) - b) := by
    have he := norm_sub_norm_le (1 : Complex) b
    rw [norm_one] at he
    linarith
  have hD : Not ((1 : Complex) - v ^ 2 = 0) := by
    intro he
    rw [he, norm_zero] at hDlow
    norm_num at hDlow
  have hb0 : Not ((1 : Complex) - b = 0) := by
    intro he
    rw [he, norm_zero] at hblow
    norm_num at hblow
  have hDiv : norm (fourthEulerRemainder r u C omega v a b / (1 - v ^ 2)) <= 2 * N := by
    rw [norm_div]
    calc
      _ <= N / norm ((1 : Complex) - v ^ 2) :=
        div_le_div_of_nonneg_right hN (norm_nonneg _)
      _ <= N / (1/2 : Real) :=
        div_le_div_of_nonneg_left hN0 (by norm_num) hDlow
      _ = _ := by ring
  have hOne : norm ((1 : Complex) - a) <= 2 := by
    have he := norm_sub_le (1 : Complex) a
    rw [norm_one] at he
    linarith
  have hLead : norm (-a ^ 2 + a * b) <= norm a ^ 2 + norm a * norm b := by
    calc
      _ <= norm (-a ^ 2) + norm (a * b) := norm_add_le _ _
      _ = _ := by rw [norm_neg, norm_pow, norm_mul]
  have hNum : norm (-a ^ 2 + a * b +
      (1 - a) * (fourthEulerRemainder r u C omega v a b / (1 - v ^ 2))) <=
      norm a ^ 2 + norm a * norm b + 4 * N := by
    have ht := norm_add_le (-a ^ 2 + a * b)
      ((1 - a) * (fourthEulerRemainder r u C omega v a b / (1 - v ^ 2)))
    rw [norm_mul] at ht
    have hm := mul_le_mul hOne hDiv (norm_nonneg _) (by norm_num : (0 : Real) <= 2)
    nlinarith
  rw [fourthEulerCorrection_identity r u C omega v a b hD hb0, norm_div]
  have hAB : 0 <= norm a ^ 2 + norm a * norm b := by positivity
  calc
    _ <= (norm a ^ 2 + norm a * norm b + 4 * N) / norm ((1 : Complex) - b) :=
      div_le_div_of_nonneg_right hNum (norm_nonneg _)
    _ <= (norm a ^ 2 + norm a * norm b + 4 * N) / (1/2 : Real) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hblow
    _ <= _ := by change _ <= 8 * (norm a ^ 2 + norm a * norm b + N); nlinarith

theorem fourthEulerCorrection_scaled (r u C omega v a b : Complex)
    (T E : Real) (hT0 : 0 <= T) (hT : T <= 1/2)
    (hTE : T <= E) (hE : E <= 1)
    (hC : norm C <= 1) (ho : norm omega <= 1)
    (hr : norm r <= T ^ 4) (hu : norm u <= T ^ 2 * E ^ 2)
    (hv : norm v <= T * E ^ 3)
    (ha : norm a <= T ^ 3 * E) (hb : norm b <= T ^ 3 * E) :
    norm (fourthEulerCorrection r u C omega v a b - 1) <=
      80 * T ^ 4 * E ^ 4 := by
  have hE0 : 0 <= E := hT0.trans hTE
  have hT1 : T <= 1 := by linarith
  have hT2 : T ^ 2 <= 1 := by nlinarith
  have hE2 : E ^ 2 <= 1 := by nlinarith
  have hE3 : E ^ 3 <= 1 := by
    calc
      _ = E ^ 2 * E := by ring
      _ <= 1 * 1 := mul_le_mul hE2 hE hE0 (by norm_num)
      _ = _ := by ring
  have hH : T ^ 3 * E <= T := by
    calc
      _ = T * (T ^ 2 * E) := by ring
      _ <= T * 1 := mul_le_mul_of_nonneg_left
        ((mul_le_mul hT2 hE hE0 (by norm_num)).trans_eq (by ring)) hT0
      _ = _ := by ring
  have hV : T * E ^ 3 <= T :=
    (mul_le_mul_of_nonneg_left hE3 hT0).trans_eq (by ring)
  have haHalf : norm a <= 1/2 := ha.trans (hH.trans hT)
  have hbHalf : norm b <= 1/2 := hb.trans (hH.trans hT)
  have hvHalf : norm v <= 1/2 := hv.trans (hV.trans hT)
  have hRaw : norm a ^ 2 + norm a * norm b + fourthEulerAllowance r u v a b <=
      2 * (T ^ 3 * E) ^ 2 +
        T ^ 4 * (T ^ 2 * E ^ 2 + (T * E ^ 3) * (T ^ 2 * E ^ 2 + 1) +
          (T * E ^ 3) ^ 2) +
        (T * E ^ 3 + (T * E ^ 3) ^ 2) * (2 * T ^ 3 * E) := by
    have hsq : norm a ^ 2 <= (T ^ 3 * E) ^ 2 := by
      nlinarith [norm_nonneg a, mul_nonneg (pow_nonneg hT0 3) hE0]
    have hab : norm a * norm b <= (T ^ 3 * E) ^ 2 := by
      have he := mul_le_mul ha hb (norm_nonneg b)
        (mul_nonneg (pow_nonneg hT0 3) hE0)
      simpa only [pow_two] using he
    have hallow : fourthEulerAllowance r u v a b <=
        T ^ 4 * (T ^ 2 * E ^ 2 + (T * E ^ 3) * (T ^ 2 * E ^ 2 + 1) +
          (T * E ^ 3) ^ 2) +
        (T * E ^ 3 + (T * E ^ 3) ^ 2) * (2 * T ^ 3 * E) := by
      unfold fourthEulerAllowance
      have hv2 : norm v ^ 2 <= (T * E ^ 3) ^ 2 := by
        nlinarith [norm_nonneg v, mul_nonneg hT0 (pow_nonneg hE0 3)]
      have hvu : norm v * (norm u + 1) <=
          (T * E ^ 3) * (T ^ 2 * E ^ 2 + 1) :=
        mul_le_mul hv (by linarith) (by positivity) (by positivity)
      have hleft := mul_le_mul hr
        (show norm u + norm v * (norm u + 1) + norm v ^ 2 <=
          T ^ 2 * E ^ 2 + (T * E ^ 3) * (T ^ 2 * E ^ 2 + 1) + (T * E ^ 3) ^ 2 by
            linarith) (by positivity) (by positivity)
      have hright := mul_le_mul
        (show norm v + norm v ^ 2 <= T * E ^ 3 + (T * E ^ 3) ^ 2 by linarith)
        (show norm a + norm b <= 2 * T ^ 3 * E by linarith)
        (by positivity) (by positivity)
      linarith
    nlinarith
  have hT2E2 : T ^ 2 <= E ^ 2 := by nlinarith
  have h6e2 : T ^ 6 * E ^ 2 <= T ^ 4 * E ^ 4 := by
    calc
      _ = (T ^ 4 * E ^ 2) * T ^ 2 := by ring
      _ <= (T ^ 4 * E ^ 2) * E ^ 2 :=
        mul_le_mul_of_nonneg_left hT2E2 (by positivity)
      _ = _ := by ring
  have h7e5 : T ^ 7 * E ^ 5 <= T ^ 4 * E ^ 4 := by
    calc
      _ = (T ^ 4 * E ^ 4) * (T ^ 3 * E) := by ring
      _ <= _ := mul_le_of_le_one_right (by positivity) (hH.trans hT1)
  have h5e3 : T ^ 5 * E ^ 3 <= T ^ 4 * E ^ 4 := by
    calc
      _ = (T ^ 4 * E ^ 3) * T := by ring
      _ <= (T ^ 4 * E ^ 3) * E := mul_le_mul_of_nonneg_left hTE (by positivity)
      _ = _ := by ring
  have h6e6 : T ^ 6 * E ^ 6 <= T ^ 4 * E ^ 4 := by
    calc
      _ = (T ^ 4 * E ^ 4) * (T ^ 2 * E ^ 2) := by ring
      _ <= _ := mul_le_of_le_one_right (by positivity)
        ((mul_le_mul hT2 hE2 (by positivity) (by norm_num)).trans_eq (by ring))
  have h5e7 : T ^ 5 * E ^ 7 <= T ^ 4 * E ^ 4 := by
    calc
      _ = (T ^ 4 * E ^ 4) * (T * E ^ 3) := by ring
      _ <= _ := mul_le_of_le_one_right (by positivity) (hV.trans hT1)
  have hpoly :
      2 * (T ^ 3 * E) ^ 2 +
        T ^ 4 * (T ^ 2 * E ^ 2 + (T * E ^ 3) * (T ^ 2 * E ^ 2 + 1) +
          (T * E ^ 3) ^ 2) +
        (T * E ^ 3 + (T * E ^ 3) ^ 2) * (2 * T ^ 3 * E) <=
      10 * T ^ 4 * E ^ 4 := by
    calc
      _ = 3 * (T ^ 6 * E ^ 2) + T ^ 7 * E ^ 5 + T ^ 5 * E ^ 3 +
          T ^ 6 * E ^ 6 + 2 * (T ^ 4 * E ^ 4) + 2 * (T ^ 5 * E ^ 7) := by ring
      _ <= _ := by nlinarith
  have hfinal := fourthEulerCorrection_norm r u C omega v a b hC ho haHalf hbHalf hvHalf
  nlinarith

def fourthZeroKernel (r u C v : Complex) : Complex :=
  r + (1 - r) * (1 - u) * (1 + C * v) / (1 - v ^ 2)

theorem fourthZeroKernel_norm (r u C v : Complex)
    (hr : norm r <= 1/16) (hr1 : norm (1 - r) <= 1)
    (hu : norm u <= 1/4) (hC : norm C <= 1) (hv : norm v <= 1/2) :
    norm (fourthZeroKernel r u C v) <= 3 := by
  have hCv : norm (C * v) <= 1/2 := by
    rw [norm_mul]
    have he := mul_le_mul hC hv (norm_nonneg v) (by norm_num : (0 : Real) <= 1)
    nlinarith
  have hu1 : norm ((1 : Complex) - u) <= 5/4 := by
    have he := norm_sub_le (1 : Complex) u
    rw [norm_one] at he
    linarith
  have hC1 : norm ((1 : Complex) + C * v) <= 3/2 := by
    have he := norm_add_le (1 : Complex) (C * v)
    rw [norm_one] at he
    linarith
  have hD : 3/4 <= norm ((1 : Complex) - v ^ 2) := by
    have he := norm_sub_norm_le (1 : Complex) (v ^ 2)
    rw [norm_one, norm_pow] at he
    nlinarith [norm_nonneg v]
  have hn : norm ((1 - r) * (1 - u) * (1 + C * v)) <= 15/8 := by
    rw [norm_mul, norm_mul]
    have hfirst := mul_le_mul hr1 hu1 (norm_nonneg _) (by norm_num : (0 : Real) <= 1)
    have he := mul_le_mul hfirst hC1 (norm_nonneg _) (by norm_num : (0 : Real) <= 1 * (5/4))
    norm_num at he
    exact he
  unfold fourthZeroKernel
  calc
    _ <= norm r + norm ((1 - r) * (1 - u) * (1 + C * v) / (1 - v ^ 2)) :=
      norm_add_le _ _
    _ <= 1/16 + (15/8 : Real) / norm ((1 : Complex) - v ^ 2) := by
      rw [norm_div]
      exact add_le_add hr (div_le_div_of_nonneg_right hn (norm_nonneg _))
    _ <= 1/16 + (15/8 : Real) / (3/4) := by
      have he : (15/8 : Real) / norm ((1 : Complex) - v ^ 2) <= (15/8 : Real) / (3/4) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD
      linarith
    _ <= _ := by norm_num

theorem fourthZeroKernel_ne_zero (r u C v : Complex)
    (hr : norm r <= 1/16) (hu : norm u <= 1/4)
    (hC : norm C <= 1) (hv : norm v <= 1/2) :
    Not (fourthZeroKernel r u C v = 0) := by
  have hCv : norm (C * v) <= 1/2 := by
    rw [norm_mul]
    have he := mul_le_mul hC hv (norm_nonneg v) (by norm_num : (0 : Real) <= 1)
    nlinarith
  have hr1 : 15/16 <= norm ((1 : Complex) - r) := by
    have he := norm_sub_norm_le (1 : Complex) r
    rw [norm_one] at he
    linarith
  have hu1 : 3/4 <= norm ((1 : Complex) - u) := by
    have he := norm_sub_norm_le (1 : Complex) u
    rw [norm_one] at he
    linarith
  have hC1 : 1/2 <= norm ((1 : Complex) + C * v) := by
    have he := norm_sub_norm_le (1 : Complex) (-(C * v))
    simpa only [norm_one, norm_neg, sub_neg_eq_add] using
      (show 1/2 <= norm ((1 : Complex) - -(C * v)) by
        rw [norm_one, norm_neg] at he
        linarith)
  have hlow : 45/128 <= norm ((1 - r) * (1 - u) * (1 + C * v)) := by
    rw [norm_mul, norm_mul]
    have hf := mul_le_mul hr1 hu1 (by norm_num : (0 : Real) <= 3/4) (norm_nonneg _)
    have he := mul_le_mul hf hC1 (by norm_num : (0 : Real) <= 1/2)
      (by positivity : 0 <= norm ((1 : Complex) - r) * norm ((1 : Complex) - u))
    norm_num at he
    exact he
  have hDup : norm ((1 : Complex) - v ^ 2) <= 5/4 := by
    have he := norm_sub_le (1 : Complex) (v ^ 2)
    rw [norm_one, norm_pow] at he
    nlinarith [norm_nonneg v]
  have hDlow : 3/4 <= norm ((1 : Complex) - v ^ 2) := by
    have he := norm_sub_norm_le (1 : Complex) (v ^ 2)
    rw [norm_one, norm_pow] at he
    nlinarith [norm_nonneg v]
  have hD : Not ((1 : Complex) - v ^ 2 = 0) := by
    intro he
    rw [he, norm_zero] at hDlow
    norm_num at hDlow
  intro hz
  have he := congrArg (fun z : Complex => z * (1 - v ^ 2)) hz
  unfold fourthZeroKernel at he
  have hprod : (1 - r) * (1 - u) * (1 + C * v) = -r * (1 - v ^ 2) := by
    field_simp at he
    linear_combination he
  rw [hprod, norm_mul, norm_neg] at hlow
  have hh := mul_le_mul hr hDup (norm_nonneg _) (by norm_num : (0 : Real) <= 1/16)
  nlinarith

end OAI.SevenEighths.ProbePowerGauss

