/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventKernel

/-! # An exact signed three-line resolvent certificate -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section
namespace PrimeFactorOscillations

open Complex

def threeLineWidthSq : Real := 9 / 64

def threeLineRadius1 : Real := 5001 / 10000

def threeLineRadius2 : Real := 7 / 10

def threeLineRadius3 : Real := 6 / 5

def threeLineWeight1 : Real := 1209493 / 1000000

def threeLineWeight2 : Real := -(1059063 / 1000000)

def threeLineWeight3 : Real := 56907 / 500000

def threeLineCharge : Real := 7004201657 / 7001400000

def threeLinePolynomialDen (r x y : Real) : Real := (r ^ 2 + y - x) ^ 2 + 4 * x * y

def threeLineNumerator (x y : Real) : Real :=
  threeLineWeight1 * threeLineRadius1 * (threeLineRadius1 ^ 2 + y - x) *
    threeLinePolynomialDen threeLineRadius2 x y * threeLinePolynomialDen threeLineRadius3 x y +
  threeLineWeight2 * threeLineRadius2 * (threeLineRadius2 ^ 2 + y - x) *
    threeLinePolynomialDen threeLineRadius1 x y * threeLinePolynomialDen threeLineRadius3 x y +
  threeLineWeight3 * threeLineRadius3 * (threeLineRadius3 ^ 2 + y - x) *
    threeLinePolynomialDen threeLineRadius1 x y * threeLinePolynomialDen threeLineRadius2 x y

def threeLineBoundary (y : Real) : Real :=
    (7098664165328288435911430833431 : Real) +
    (-45479514152778610533352385212800 : Real) * y ^ 1 +
    (26778452454098204696759162880000 : Real) * y ^ 2 +
    (165401944593302074032758784000000 : Real) * y ^ 3 +
    (12900215079942957465600000000000 : Real) * y ^ 4 +
    (82042306560000000000000000000 : Real) * y ^ 5

def threeLineCorrection (q y : Real) : Real :=
  q * ((91255181734902560966948254147200 : Real) + (1262282716760160253614896056320000 : Real) * y +
      (2159245231666356509596041216000000 : Real) * y ^ 2 + (50123828055516797337600000000000 : Real) * y ^ 3) +
    q * (246126919680000000000000000000 : Real) * (threeLineWidthSq - q) *
      (threeLineWidthSq ^ 2 + threeLineWidthSq * q + q ^ 2) * y +
    q * (126209607061959509606400000000000 : Real) * (threeLineWidthSq - q) * y ^ 2 +
    q ^ 2 * ((259197159561003190334932346880000 : Real) + (2120312077664507304680841216000000 : Real) * y +
      (164084613120000000000000000000 : Real) * y ^ 3) +
    q ^ 3 * ((165213705955061210083958784000000 : Real) + (50308423245276797337600000000000 : Real) * y +
      (164084613120000000000000000000 : Real) * y ^ 2) +
    q ^ 4 * (12842529083142957465600000000000 : Real) + q ^ 5 * (82042306560000000000000000000 : Real) +
    (246126919680000000000000000000 : Real) * (threeLineWidthSq - q) * y ^ 4

theorem threeLineNumerator_certificate (q y : Real) :
    (819200000000000000000000000000000 : Real) * threeLineNumerator (threeLineWidthSq - q) y =
      threeLineBoundary y + threeLineCorrection q y := by
  unfold threeLineNumerator threeLinePolynomialDen threeLineWidthSq threeLineRadius1
    threeLineRadius2 threeLineRadius3 threeLineWeight1 threeLineWeight2 threeLineWeight3
    threeLineBoundary threeLineCorrection
  unfold threeLineWidthSq
  ring

theorem threeLineBoundary_pos (y : Real) (hy : 0 <= y) : 0 < threeLineBoundary y := by
  let d : Real := 26778452454098204696759162880000
  let p0 : Real := 37315874381145680482638210231
  let p1 : Real := -269557483188934462230531772800
  let R : Real := (165401944593302074032758784000000 : Real) * (y + 1 / 2) +
    (12900215079942957465600000000000 : Real) * (y ^ 2 + y / 2 + 3 / 16) +
    (82042306560000000000000000000 : Real) * (y ^ 3 + y ^ 2 / 2 + 3 * y / 16 + 1 / 16)
  have hd : 0 < d := by norm_num [d]
  have hR : 0 <= R := by dsimp only [R]; positivity
  have hdisc : 0 < 4 * d * p0 - p1 ^ 2 := by norm_num [d, p0, p1]
  have hid : 4 * d * threeLineBoundary y =
      (2 * d * (y - 1 / 4) + p1) ^ 2 + (4 * d * p0 - p1 ^ 2) +
        4 * d * (y - 1 / 4) ^ 2 * R := by
    dsimp only [d, p0, p1, R, threeLineBoundary]
    ring
  have hr : 0 <= 4 * d * (y - 1 / 4) ^ 2 * R := by positivity
  have hp : 0 < 4 * d * threeLineBoundary y := by
    rw [hid]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (sq_nonneg _) hdisc) hr
  by_contra h
  have hn : threeLineBoundary y <= 0 := le_of_not_gt h
  have hbad : 4 * d * threeLineBoundary y <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
  exact (not_lt_of_ge hbad) hp

theorem threeLineCorrection_nonneg (q y : Real) (hq : 0 <= q)
    (hqW : q <= threeLineWidthSq) (hy : 0 <= y) : 0 <= threeLineCorrection q y := by
  have hqC : 0 <= threeLineWidthSq - q := sub_nonneg.mpr hqW
  have hW : 0 <= threeLineWidthSq := by norm_num [threeLineWidthSq]
  unfold threeLineCorrection
  positivity

theorem threeLineNumerator_pos (x y : Real) (hx : 0 <= x)
    (hxW : x <= threeLineWidthSq) (hy : 0 <= y) : 0 < threeLineNumerator x y := by
  let q : Real := threeLineWidthSq - x
  have hq : 0 <= q := sub_nonneg.mpr hxW
  have hqW : q <= threeLineWidthSq := by dsimp only [q]; linarith only [hx]
  have hc := threeLineCorrection_nonneg q y hq hqW hy
  have hb := threeLineBoundary_pos y hy
  have hid := threeLineNumerator_certificate q y
  have he : threeLineWidthSq - q = x := by dsimp only [q]; ring
  rw [he] at hid
  have hp : 0 < (819200000000000000000000000000000 : Real) * threeLineNumerator x y := by
    rw [hid]
    exact add_pos_of_pos_of_nonneg hb hc
  by_contra h
  have hn : threeLineNumerator x y <= 0 := le_of_not_gt h
  have hbad : (819200000000000000000000000000000 : Real) * threeLineNumerator x y <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn
  exact (not_lt_of_ge hbad) hp

def threeLineKernel (u v : Real) : Real :=
  threeLineWeight1 * pairedResolventMean threeLineRadius1 u v +
    threeLineWeight2 * pairedResolventMean threeLineRadius2 u v +
    threeLineWeight3 * pairedResolventMean threeLineRadius3 u v

def threeLineDiagonal (q : Real) : Real :=
  ((47280796675390397583/53344000000000000000 : Real) - 7 / 64 * (1329922720112744657/700140000000000000 : Real) +
    49 / 4096 * threeLineCharge) +
  ((1329922720112744657/700140000000000000 : Real) - 7 / 32 * threeLineCharge) * q + threeLineCharge * q ^ 2

def threeLineLeadingCoefficient : Real :=
  (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / (2 * threeLineCharge)

theorem threeLineCharge_pos : 0 < threeLineCharge := by norm_num [threeLineCharge]

theorem threeLinePolynomialDen_eq (r u v : Real) :
    threeLinePolynomialDen r (u ^ 2) (v ^ 2) = pairedResolventDen r u v := by
  unfold threeLinePolynomialDen pairedResolventDen
  ring

theorem threeLineKernel_mul_den (u v : Real) (hu : abs u < threeLineRadius1) :
    threeLineKernel u v * (pairedResolventDen threeLineRadius1 u v *
      pairedResolventDen threeLineRadius2 u v * pairedResolventDen threeLineRadius3 u v) =
        threeLineNumerator (u ^ 2) (v ^ 2) := by
  have h2 : abs u < threeLineRadius2 := hu.trans (by norm_num [threeLineRadius1, threeLineRadius2])
  have h3 : abs u < threeLineRadius3 := hu.trans (by norm_num [threeLineRadius1, threeLineRadius3])
  have hd1 := pairedResolventDen_pos threeLineRadius1 u v hu
  have hd2 := pairedResolventDen_pos threeLineRadius2 u v h2
  have hd3 := pairedResolventDen_pos threeLineRadius3 u v h3
  unfold threeLineKernel threeLineNumerator
  rw [pairedResolventMean_formula _ _ _ hu, pairedResolventMean_formula _ _ _ h2,
    pairedResolventMean_formula _ _ _ h3]
  simp only [threeLinePolynomialDen_eq]
  field_simp [hd1.ne', hd2.ne', hd3.ne'] <;> ring

theorem threeLineKernel_pos (u v : Real) (hu : abs u <= 3 / 8) :
    0 < threeLineKernel u v := by
  have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
  have h2 : abs u < threeLineRadius2 := hu.trans_lt (by norm_num [threeLineRadius2])
  have h3 : abs u < threeLineRadius3 := hu.trans_lt (by norm_num [threeLineRadius3])
  have hx : u ^ 2 <= threeLineWidthSq := by
    have hab := abs_le.mp hu
    have hm : 0 <= (3 / 8 - u) * (3 / 8 + u) :=
      mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
    unfold threeLineWidthSq
    nlinarith only [hm]
  have hn := threeLineNumerator_pos (u ^ 2) (v ^ 2) (sq_nonneg u) hx (sq_nonneg v)
  have hd : 0 < pairedResolventDen threeLineRadius1 u v *
      pairedResolventDen threeLineRadius2 u v * pairedResolventDen threeLineRadius3 u v :=
    mul_pos (mul_pos (pairedResolventDen_pos _ _ _ h1)
      (pairedResolventDen_pos _ _ _ h2)) (pairedResolventDen_pos _ _ _ h3)
  have hp : 0 < threeLineKernel u v * (pairedResolventDen threeLineRadius1 u v *
      pairedResolventDen threeLineRadius2 u v * pairedResolventDen threeLineRadius3 u v) := by
    rw [threeLineKernel_mul_den u v h1]
    exact hn
  have hscaled : 0 * (pairedResolventDen threeLineRadius1 u v *
      pairedResolventDen threeLineRadius2 u v * pairedResolventDen threeLineRadius3 u v) <
        threeLineKernel u v * (pairedResolventDen threeLineRadius1 u v *
          pairedResolventDen threeLineRadius2 u v * pairedResolventDen threeLineRadius3 u v) := by
    simpa using hp
  exact (mul_lt_mul_iff_of_pos_right hd).mp hscaled

theorem resolventSquareMargin_pos (r u : Real) (hu : abs u < r) : 0 < r ^ 2 - u ^ 2 := by
  have hh := abs_lt.mp hu
  calc
    0 < (r - u) * (r + u) := mul_pos (by linarith only [hh.2]) (by linarith only [hh.1])
    _ = r ^ 2 - u ^ 2 := by ring

theorem pairedResolventMean_at_zero (r u : Real) (hu : abs u < r) :
    pairedResolventMean r u 0 = r / (r ^ 2 - u ^ 2) := by
  have hd := resolventSquareMargin_pos r u hu
  have he : pairedResolventDen r u 0 = (r ^ 2 - u ^ 2) ^ 2 := by
    unfold pairedResolventDen
    ring
  rw [pairedResolventMean_formula r u 0 hu, he]
  norm_num only [zero_pow, add_zero]
  field_simp [hd.ne'] <;> ring

theorem threeLineDiagonal_pos (q : Real) (hq : 0 <= q) : 0 < threeLineDiagonal q := by
  have h0 : 0 < ((47280796675390397583/53344000000000000000 : Real) - 7 / 64 * (1329922720112744657/700140000000000000 : Real) +
      49 / 4096 * threeLineCharge) := by norm_num [threeLineCharge]
  have h1 : 0 < ((1329922720112744657/700140000000000000 : Real) - 7 / 32 * threeLineCharge) := by
    norm_num [threeLineCharge]
  unfold threeLineDiagonal
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg h0 (mul_nonneg h1.le hq))
    (mul_nonneg threeLineCharge_pos.le (sq_nonneg q))

theorem threeLineKernel_same_height_ge (u : Real) (hu : abs u <= 1 / 2) :
    threeLineCharge <= threeLineKernel u 0 := by
  have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
  have h2 : abs u < threeLineRadius2 := hu.trans_lt (by norm_num [threeLineRadius2])
  have h3 : abs u < threeLineRadius3 := hu.trans_lt (by norm_num [threeLineRadius3])
  have hd1 := resolventSquareMargin_pos _ _ h1
  have hd2 := resolventSquareMargin_pos _ _ h2
  have hd3 := resolventSquareMargin_pos _ _ h3
  let D : Real := (threeLineRadius1 ^ 2 - u ^ 2) * (threeLineRadius2 ^ 2 - u ^ 2) *
    (threeLineRadius3 ^ 2 - u ^ 2)
  have hD : 0 < D := mul_pos (mul_pos hd1 hd2) hd3
  have hq : 0 <= 1 / 4 - u ^ 2 := by
    have hh := abs_le.mp hu
    have hm : 0 <= (1 / 2 - u) * (1 / 2 + u) :=
      mul_nonneg (by linarith only [hh.2]) (by linarith only [hh.1])
    nlinarith only [hm]
  have hid : (threeLineKernel u 0 - threeLineCharge) * D =
      u ^ 2 * threeLineDiagonal (1 / 4 - u ^ 2) := by
    unfold threeLineKernel
    rw [pairedResolventMean_at_zero _ _ h1, pairedResolventMean_at_zero _ _ h2,
      pairedResolventMean_at_zero _ _ h3]
    dsimp only [D]
    field_simp [hd1.ne', hd2.ne', hd3.ne']
    unfold threeLineDiagonal threeLineRadius1 threeLineRadius2 threeLineRadius3
      threeLineWeight1 threeLineWeight2 threeLineWeight3 threeLineCharge
    ring
  have hp : 0 <= (threeLineKernel u 0 - threeLineCharge) * D := by
    rw [hid]
    exact mul_nonneg (sq_nonneg u) (threeLineDiagonal_pos _ hq).le
  have hscaled : 0 * D <= (threeLineKernel u 0 - threeLineCharge) * D := by simpa using hp
  exact sub_nonneg.mp ((mul_le_mul_iff_of_pos_right hD).mp hscaled)

theorem threeLineLeadingCoefficient_eq :
    threeLineLeadingCoefficient = 4625194854 / 35021008285 := by
  norm_num [threeLineLeadingCoefficient, threeLineWeight1, threeLineWeight2,
    threeLineWeight3, threeLineCharge]

theorem threeLineLeadingCoefficient_lt : threeLineLeadingCoefficient < 1321 / 10000 := by
  rw [threeLineLeadingCoefficient_eq]
  norm_num

end PrimeFactorOscillations
