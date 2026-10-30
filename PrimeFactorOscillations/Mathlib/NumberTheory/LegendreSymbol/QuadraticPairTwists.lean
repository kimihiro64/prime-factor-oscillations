/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairEuler

/-!
# Shifted elliptic twist compensation

The seven labelled character factors balance exactly, including repeated
labels. The two active zero-discriminant rows determine exponents zero,
two or four. The scalar power estimates retain the linear trace correction.
The full corrected quotient is positive and has inverse-square local defect
uniformly on the stated square-root trace range.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open scoped BigOperators

namespace FiniteField.QuadraticPairEuler

def activeRows (e f x y : Real) : Nat :=
  (if x = 1 /\ f = -1 then 1 else 0) + (if y = 1 /\ e = -1 then 1 else 0)

def shiftedLocal (r s v : Real) : Real := 1 - v * r + s

theorem correction_eq_rows (e f x y : Real)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    (1 + x) * (1 - f) + (1 + y) * (1 - e) =
      4 * (activeRows e f x y : Real) := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [activeRows]

theorem shifted_twist_balance (r s e f x y : Real)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    (shiftedLocal r s 1) ^ 2 * shiftedLocal r s x * shiftedLocal r s y *
        (shiftedLocal r s (-1)) ^ (2 * activeRows e f x y) =
      shiftedLocal r s e * shiftedLocal r s f *
        shiftedLocal r s (f * x) * shiftedLocal r s (e * y) *
          (shiftedLocal r s 1) ^ (2 * activeRows e f x y) := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [shiftedLocal, activeRows] <;> ring_nf <;> simp

def ratioIncrement (r s : Real) : Real := (1 - r + s) / (1 + r + s) - 1

theorem ratio_denominator_lower (r s t : Real)
    (ht0 : 0 <= t) (ht : t <= 1 / 16) (hr : |r| <= t / 2) (hs : 0 <= s) :
    3 / 4 <= 1 + r + s := by
  linarith [neg_le_abs r]

theorem ratio_increment_bound (r s t : Real)
    (ht0 : 0 <= t) (ht : t <= 1 / 16) (hr : |r| <= t / 2) (hs : 0 <= s) :
    |ratioIncrement r s| <= 3 * |r| := by
  have hd := ratio_denominator_lower r s t ht0 ht hr hs
  have hdpos : 0 < 1 + r + s := by linarith
  have hdne := ne_of_gt hdpos
  have heq : ratioIncrement r s = -2 * r / (1 + r + s) := by
    unfold ratioIncrement
    field_simp [hdne]
    <;> ring
  rw [heq, abs_div, abs_of_pos hdpos]
  have hi : 2 * |r| <= (3 * |r|) * (1 + r + s) := by
    nlinarith [abs_nonneg r]
  calc
    |-2 * r| / (1 + r + s) = (2 * |r|) / (1 + r + s) := by
      congr 1
      simp [abs_mul]
    _ <= ((3 * |r|) * (1 + r + s)) / (1 + r + s) :=
      div_le_div_of_nonneg_right hi (le_of_lt hdpos)
    _ = _ := by field_simp [hdne]

theorem ratio_linear_bound (r s t : Real)
    (ht0 : 0 <= t) (ht : t <= 1 / 16) (hr : |r| <= t / 2)
    (hs : 0 <= s) (hst : s <= t) :
    |ratioIncrement r s + 2 * r| <= 3 * t ^ 2 := by
  have hd := ratio_denominator_lower r s t ht0 ht hr hs
  have hdpos : 0 < 1 + r + s := by linarith
  have hdne := ne_of_gt hdpos
  have heq : ratioIncrement r s + 2 * r = 2 * r * (r + s) / (1 + r + s) := by
    unfold ratioIncrement
    field_simp [hdne]
    <;> ring
  have hsum : |r + s| <= |r| + s := by
    apply abs_le.mpr
    constructor
    . linarith [neg_le_abs r]
    . linarith [le_abs_self r]
  have habs0 : 0 <= |r| := abs_nonneg r
  have hmul := mul_le_mul hr (add_le_add hr hst)
    (add_nonneg habs0 hs) (by linarith : 0 <= t / 2)
  have hi : 2 * |r| * |r + s| <=
      (4 * |r| * (|r| + s)) * (1 + r + s) := by
    have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 <= 2 * |r|)
    have hp := mul_le_mul_of_nonneg_left
      (show (2 : Real) <= 4 * (1 + r + s) by linarith)
      (mul_nonneg habs0 (add_nonneg habs0 hs))
    nlinarith
  rw [heq, abs_div, abs_of_pos hdpos]
  calc
    |2 * r * (r + s)| / (1 + r + s) =
        (2 * |r| * |r + s|) / (1 + r + s) := by
      congr 1
      simp [abs_mul]
    _ <= ((4 * |r| * (|r| + s)) * (1 + r + s)) / (1 + r + s) :=
      div_le_div_of_nonneg_right hi (le_of_lt hdpos)
    _ = 4 * |r| * (|r| + s) := by field_simp [hdne]
    _ <= 3 * t ^ 2 := by nlinarith only [hmul]

theorem binomial_remainder_bound (v : Real) (hv : |v| <= 1 / 8)
    (k : Nat) (hk : k = 0 \/ k = 2 \/ k = 4) :
    |(1 + v) ^ k - 1 - (k : Real) * v| <= 8 * v ^ 2 := by
  have hvU : v <= 1 / 8 := le_trans (le_abs_self v) hv
  have hvL : -(1 / 8 : Real) <= v := by linarith [neg_le_abs v]
  have hvSq : v ^ 2 <= 1 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvU) (sub_nonneg.mpr hvL)]
  rcases hk with hk | hk | hk
  . subst k
    norm_num
    positivity
  . subst k
    have heq : (1 + v) ^ 2 - 1 - ((2 : Nat) : Real) * v = v ^ 2 := by norm_num <;> ring
    rw [heq, abs_of_nonneg (sq_nonneg v)]
    nlinarith [sq_nonneg v]
  . subst k
    have heq : (1 + v) ^ 4 - 1 - ((4 : Nat) : Real) * v =
        v ^ 2 * (v ^ 2 + 4 * v + 6) := by norm_num <;> ring
    have hc0 : 0 <= v ^ 2 + 4 * v + 6 := by nlinarith [sq_nonneg v]
    have hc : v ^ 2 + 4 * v + 6 <= 8 := by nlinarith
    rw [heq, abs_mul, abs_of_nonneg (sq_nonneg v), abs_of_nonneg hc0]
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg v)]

theorem ratio_power_bound (r s t : Real)
    (ht0 : 0 <= t) (ht : t <= 1 / 16) (hr : |r| <= t / 2)
    (hs : 0 <= s) (hst : s <= t)
    (k : Nat) (hk : k = 0 \/ k = 2 \/ k = 4) :
    |((1 - r + s) / (1 + r + s)) ^ k - 1 + 2 * (k : Real) * r| <=
      32 * t ^ 2 := by
  let v : Real := ratioIncrement r s
  have hv0 : |v| <= 3 * |r| := ratio_increment_bound r s t ht0 ht hr hs
  have hvT : |v| <= 3 * t / 2 := by linarith
  have hv : |v| <= 1 / 8 := by linarith
  have hvU : v <= 3 * t / 2 := le_trans (le_abs_self v) hvT
  have hvL : -(3 * t / 2) <= v := by linarith [neg_le_abs v]
  have hvSq : v ^ 2 <= 9 * t ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvU) (sub_nonneg.mpr hvL)]
  have hk0 : 0 <= (k : Real) := Nat.cast_nonneg k
  have hk4 : (k : Real) <= 4 := by
    rcases hk with hk | hk | hk <;> rw [hk] <;> norm_num
  let A : Real := (1 + v) ^ k - 1 - (k : Real) * v
  let B : Real := (k : Real) * (v + 2 * r)
  have hA : |A| <= 8 * v ^ 2 := binomial_remainder_bound v hv k hk
  have hlin : |v + 2 * r| <= 3 * t ^ 2 := ratio_linear_bound r s t ht0 ht hr hs hst
  have hB : |B| <= 12 * t ^ 2 := by
    dsimp only [B]
    rw [abs_mul, abs_of_nonneg hk0]
    have hm := mul_le_mul_of_nonneg_left hlin hk0
    have hc := mul_le_mul_of_nonneg_right hk4 (by positivity : 0 <= 3 * t ^ 2)
    nlinarith only [hm, hc]
  have htri : |A + B| <= |A| + |B| := by
    apply abs_le.mpr
    constructor
    . linarith [neg_le_abs A, neg_le_abs B]
    . linarith [le_abs_self A, le_abs_self B]
  have hV : (1 - r + s) / (1 + r + s) = 1 + v := by
    dsimp [v, ratioIncrement]
    ring
  have heq : ((1 - r + s) / (1 + r + s)) ^ k - 1 + 2 * (k : Real) * r =
      A + B := by
    dsimp only [A, B]
    rw [hV]
    ring
  rw [heq]
  nlinarith only [hA, hB, htri, hvSq, sq_nonneg t]

theorem ratio_power_lower (r s t : Real)
    (ht0 : 0 <= t) (ht : t <= 1 / 16) (hr : |r| <= t / 2)
    (hs : 0 <= s) (k : Nat) (hk : k = 0 \/ k = 2 \/ k = 4) :
    1 / 2 <= ((1 - r + s) / (1 + r + s)) ^ k := by
  let v : Real := ratioIncrement r s
  let u : Real := (1 - r + s) / (1 + r + s)
  have hv0 : |v| <= 3 * |r| := ratio_increment_bound r s t ht0 ht hr hs
  have hv : |v| <= 1 / 8 := by linarith
  have hvL : -(1 / 8 : Real) <= v := by linarith [neg_le_abs v]
  have hu : (7 / 8 : Real) <= u := by
    have heq : u = 1 + v := by dsimp [u, v, ratioIncrement]; ring
    rw [heq]
    linarith
  have hu0 : 0 <= u := by linarith
  have hu2 : (49 / 64 : Real) <= u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 <= u + 7 / 8)]
  have hu4 : (2401 / 4096 : Real) <= u ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2)
      (by nlinarith [sq_nonneg u] : 0 <= u ^ 2 + 49 / 64)]
  change (1 / 2 : Real) <= u ^ k
  rcases hk with hk | hk | hk
  . subst k
    norm_num
  . subst k
    linarith only [hu2]
  . subst k
    linarith only [hu4]

def scalarTwist (p a : Real) (k : Nat) : Real :=
  ((1 - a / p ^ 2 + 1 / p ^ 3) / (1 + a / p ^ 2 + 1 / p ^ 3)) ^ k

def twistCorrection (p a e f x y : Real) : Real :=
  scalarTwist p a (2 * activeRows e f x y)

def correctedCarrier (p a e f x y : Real) : Real :=
  carrier p a e f x y / twistCorrection p a e f x y

private theorem scaled_parameters (p a : Real) (hp : 16 <= p) (ha : |a| <= p / 2) :
    0 <= 1 / p /\ 1 / p <= (1 / 16 : Real) /\
      |a / p ^ 2| <= (1 / p) / 2 /\ 0 <= 1 / p ^ 3 /\ 1 / p ^ 3 <= 1 / p := by
  have hp0 : 0 < p := by linarith
  have hpne := ne_of_gt hp0
  have ht0 : 0 <= (1 : Real) / p := by positivity
  have ht : (1 : Real) / p <= 1 / 16 := by
    calc
      (1 : Real) / p = 16 / (16 * p) := by field_simp [hpne]
      _ <= p / (16 * p) := div_le_div_of_nonneg_right hp (by positivity)
      _ = 1 / 16 := by field_simp [hpne]
  have hr : |a / p ^ 2| <= (1 / p) / 2 := by
    rw [abs_div, abs_of_pos (sq_pos_of_ne_zero hpne)]
    calc
      |a| / p ^ 2 <= (p / 2) / p ^ 2 :=
        div_le_div_of_nonneg_right ha (sq_nonneg p)
      _ = _ := by field_simp [hpne]
  have hs : 0 <= (1 : Real) / p ^ 3 := by positivity
  have hpow : p <= p ^ 3 := by
    have h1 : 0 <= p - 1 := by linarith
    have h2 : 0 <= p ^ 2 + p := by positivity
    nlinarith [mul_nonneg h1 h2]
  have hst : (1 : Real) / p ^ 3 <= 1 / p := by
    calc
      (1 : Real) / p ^ 3 = p / p ^ 4 := by field_simp [hpne]
      _ <= p ^ 3 / p ^ 4 := div_le_div_of_nonneg_right hpow (by positivity)
      _ = 1 / p := by field_simp [hpne]
  exact And.intro ht0 (And.intro ht (And.intro hr (And.intro hs hst)))

theorem scalarTwist_error (p a : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (k : Nat) (hk : k = 0 \/ k = 2 \/ k = 4) :
    |scalarTwist p a k - 1 + 2 * (k : Real) * (a / p ^ 2)| <= 32 / p ^ 2 := by
  have h := scaled_parameters p a hp ha
  have hb := ratio_power_bound (a / p ^ 2) (1 / p ^ 3) (1 / p)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 k hk
  have hpne : Not (p = 0) := ne_of_gt (by linarith : 0 < p)
  have heq : (32 : Real) * (1 / p) ^ 2 = 32 / p ^ 2 := by field_simp [hpne]
  rw [heq] at hb
  exact hb

theorem scalarTwist_lower (p a : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (k : Nat) (hk : k = 0 \/ k = 2 \/ k = 4) :
    1 / 2 <= scalarTwist p a k := by
  have h := scaled_parameters p a hp ha
  exact ratio_power_lower (a / p ^ 2) (1 / p ^ 3) (1 / p)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 k hk

theorem activeRows_twice_cases (e f x y : Real)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    2 * activeRows e f x y = 0 \/ 2 * activeRows e f x y = 2 \/
      2 * activeRows e f x y = 4 := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [activeRows]

theorem trace_half_of_square (p a : Real) (hp : 16 <= p) (hasq : a ^ 2 <= 4 * p) :
    |a| <= p / 2 := by
  have hp0 : 0 < p := by linarith
  have hpSq : 4 * p <= p ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (le_of_lt hp0)]
  have upper (v : Real) (hv : v ^ 2 <= 4 * p) : v <= p / 2 := by
    by_contra hn
    have hd : 0 < v - p / 2 := by linarith
    have hs : 0 < v + p / 2 := by linarith
    nlinarith [mul_pos hd hs]
  apply abs_le.mpr
  constructor
  . have hn : (-a) ^ 2 <= 4 * p := by nlinarith only [hasq]
    linarith [upper (-a) hn]
  . exact upper a hasq

theorem corrected_carrier_bound
    (p a e f x y : Real) (hp : 16 <= p) (hasq : a ^ 2 <= 4 * p)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |correctedCarrier p a e f x y - 1| <= 32832 / p ^ 2 := by
  have ha := trace_half_of_square p a hp hasq
  let k : Nat := 2 * activeRows e f x y
  have hk : k = 0 \/ k = 2 \/ k = 4 := activeRows_twice_cases e f x y he hf hx hy
  have hR := carrier_refined_defect p a e f x y hp ha hasq he hf hx hy
  have hT := scalarTwist_error p a hp ha k hk
  have hTl := scalarTwist_lower p a hp ha k hk
  have hZ : correction e f x y = 2 * (k : Real) := by
    calc
      correction e f x y = 4 * (activeRows e f x y : Real) := by
        simpa only [correction] using correction_eq_rows e f x y he hf hx hy
      _ = _ := by dsimp [k]; push_cast; ring
  have hcenter : 2 * (k : Real) * (a / p ^ 2) = correction e f x y * a / p ^ 2 := by
    rw [hZ]
    ring
  rw [hcenter] at hT
  change |twistCorrection p a e f x y - 1 + correction e f x y * a / p ^ 2| <=
    32 / p ^ 2 at hT
  change (1 / 2 : Real) <= twistCorrection p a e f x y at hTl
  have hTpos : 0 < twistCorrection p a e f x y := by linarith
  have hTne := ne_of_gt hTpos
  have hp0 : 0 < p := by linarith
  have hpne := ne_of_gt hp0
  have hdiff : |carrier p a e f x y - twistCorrection p a e f x y| <=
      16416 / p ^ 2 := by
    have hRb := abs_le.mp hR
    have hTb := abs_le.mp hT
    have hRlo := hRb.1
    have hRhi := hRb.2
    have hTlo := hTb.1
    have hThi := hTb.2
    ring_nf at hRlo hRhi hTlo hThi
    apply abs_le.mpr
    constructor <;> ring_nf <;> linarith only [hRlo, hRhi, hTlo, hThi]
  have hineq : |carrier p a e f x y - twistCorrection p a e f x y| <=
      (32832 / p ^ 2) * twistCorrection p a e f x y := by
    calc
      _ <= 16416 / p ^ 2 := hdiff
      _ = (32832 / p ^ 2) * (1 / 2) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hTl (by positivity)
  have heq : correctedCarrier p a e f x y - 1 =
      (carrier p a e f x y - twistCorrection p a e f x y) /
        twistCorrection p a e f x y := by
    unfold correctedCarrier
    field_simp [hTne]
  rw [heq, abs_div, abs_of_pos hTpos]
  calc
    _ <= ((32832 / p ^ 2) * twistCorrection p a e f x y) /
        twistCorrection p a e f x y :=
      div_le_div_of_nonneg_right hineq (le_of_lt hTpos)
    _ = _ := by field_simp [hTne]

theorem corrected_carrier_pos
    (p a e f x y : Real) (hp : 16 <= p) (hasq : a ^ 2 <= 4 * p)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    0 < correctedCarrier p a e f x y := by
  have ha := trace_half_of_square p a hp hasq
  have hk := activeRows_twice_cases e f x y he hf hx hy
  have hl := scalarTwist_lower p a hp ha (2 * activeRows e f x y) hk
  have ht : 0 < twistCorrection p a e f x y := by
    change (1 / 2 : Real) <= twistCorrection p a e f x y at hl
    linarith
  exact div_pos (carrier_pos p a e f x y hp ha he hf hx hy) ht

theorem twistCorrection_eq_seven
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    let r : Real := a / p ^ 2
    let s : Real := 1 / p ^ 3
    twistCorrection p a e f x y =
      ((1 - r + s) ^ 2 * (1 - x * r + s) * (1 - y * r + s)) /
        ((1 - e * r + s) * (1 - f * r + s) *
          (1 - (f * x) * r + s) * (1 - (e * y) * r + s)) := by
  let r : Real := a / p ^ 2
  let s : Real := 1 / p ^ 3
  let k : Nat := 2 * activeRows e f x y
  change ((1 - r + s) / (1 + r + s)) ^ k =
    ((1 - r + s) ^ 2 * (1 - x * r + s) * (1 - y * r + s)) /
      ((1 - e * r + s) * (1 - f * r + s) *
        (1 - (f * x) * r + s) * (1 - (e * y) * r + s))
  have hl := scalarTwist_lower p a hp ha 2 (Or.inr (Or.inl rfl))
  change (1 / 2 : Real) <= ((1 - r + s) / (1 + r + s)) ^ 2 at hl
  have hA : Not (1 - r + s = 0) := by
    intro hz
    have h := hl
    norm_num [hz] at h
  have hB : Not (1 + r + s = 0) := by
    intro hz
    have h := hl
    norm_num [hz] at h
  have hlocal (v : Real) (hv : v = 1 \/ v = -1) :
      Not (1 - v * r + s = 0) := by
    rcases hv with h | h
    . rw [h, one_mul]
      exact hA
    . rw [h, neg_one_mul, sub_neg_eq_add]
      exact hB
  have hfx : f * x = 1 \/ f * x = -1 := by
    rcases hf with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num
  have hey : e * y = 1 \/ e * y = -1 := by
    rcases he with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
  have hDen : Not ((1 - e * r + s) * (1 - f * r + s) *
      (1 - (f * x) * r + s) * (1 - (e * y) * r + s) = 0) :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hlocal e he) (hlocal f hf))
      (hlocal (f * x) hfx)) (hlocal (e * y) hey)
  have hb := shifted_twist_balance r s e f x y he hf hx hy
  simp only [shiftedLocal, one_mul, neg_one_mul, sub_neg_eq_add] at hb
  have divide_identity (A B N D : Real) (k : Nat) (hD : Not (D = 0))
      (hB : Not (B = 0)) (h : N * B ^ k = D * A ^ k) :
      (A / B) ^ k = N / D := by
    rw [div_pow]
    field_simp [hD, pow_ne_zero k hB]
    nlinarith only [h]
  exact divide_identity _ _ _ _ k hDen hB hb

end FiniteField.QuadraticPairEuler
