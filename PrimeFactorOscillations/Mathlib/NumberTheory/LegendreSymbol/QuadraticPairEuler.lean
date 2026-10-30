/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Euler comparison for conditional quadratic-pair packets

The full rational local quotient retains the point trace and both
zero-discriminant corrections. Its signed degree-four numerator defect
has no uncancelled degree-three term. Uniform bounds are proved on the
explicit real trace range, including positivity of every denominator.

The square-root trace hypothesis is an input to the final scalar bound;
this module does not claim to formalize Hasse's theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section

namespace FiniteField.QuadraticPairEuler

def correction (e f x y : Real) : Real :=
  (1 + x) * (1 - f) + (1 + y) * (1 - e)

def offset (e f : Real) : Real := 3 - e - f

def numerator (p a e f x y : Real) : Real :=
  (p + 1 - a - correction e f x y) * (p - 1) * (p - f * x) * (p - e * y)

def denominator (p a e f x y : Real) : Real :=
  (p - offset e f) * (p + 1 - a) * (p - x) * (p - y)

noncomputable def carrier (p a e f x y : Real) : Real :=
  numerator p a e f x y / denominator p a e f x y

theorem signed_defect (p a e f x y : Real) :
    numerator p a e f x y - denominator p a e f x y =
      -correction e f x y * a * p ^ 2 +
      (correction e f x y * (2 + f * x + e * y) +
        (f * x + e * y + e * f * x * y - offset e f * (x + y) - x * y)) * p ^ 2 +
      (-correction e f x y * (f * x + e * y + e * f * x * y) +
        (1 - a) * (f * x + e * y + e * f * x * y -
          offset e f * (x + y) - x * y) +
        x * y * (offset e f - e * f)) * p +
      correction e f x y * e * f * x * y +
        (1 - a) * x * y * (offset e f - e * f) := by
  unfold numerator denominator correction offset
  ring

theorem numerator_sub_denominator_bound
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |numerator p a e f x y - denominator p a e f x y| <=
      (8 * |a| + 56) * p ^ 2 := by
  have hp0 : 0 <= p := by linarith
  have hp2 : 0 <= p ^ 2 := sq_nonneg p
  have habs0 : 0 <= |a| := abs_nonneg a
  have ha1 : a <= |a| := le_abs_self a
  have ha2 : -a <= |a| := neg_le_abs a
  have hap : a * p <= |a| * p := mul_le_mul_of_nonneg_right ha1 hp0
  have hnap : -a * p <= |a| * p := mul_le_mul_of_nonneg_right ha2 hp0
  have hap2 : a * p ^ 2 <= |a| * p ^ 2 :=
    mul_le_mul_of_nonneg_right ha1 hp2
  have hnap2 : -a * p ^ 2 <= |a| * p ^ 2 :=
    mul_le_mul_of_nonneg_right ha2 hp2
  have habsp : |a| * p <= p ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right ha hp0]
  have hp2large : 16 * p <= p ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hp0]
  rw [abs_le]
  constructor <;>
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [numerator, denominator, correction, offset] <;> nlinarith

theorem denominator_lower
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    p ^ 4 / 16 <= denominator p a e f x y := by
  have hp0 : 0 <= p / 2 := by linarith
  have hd : p / 2 <= p - offset e f := by
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      norm_num [offset] <;> linarith
  have hA : p / 2 <= p + 1 - a := by linarith [le_abs_self a]
  have hX : p / 2 <= p - x := by rcases hx with rfl | rfl <;> linarith
  have hY : p / 2 <= p - y := by rcases hy with rfl | rfl <;> linarith
  have hfirst : (p / 2) * (p / 2) <=
      (p - offset e f) * (p + 1 - a) :=
    mul_le_mul hd hA hp0 (le_trans hp0 hd)
  have hsecond : (p / 2) * (p / 2) <= (p - x) * (p - y) :=
    mul_le_mul hX hY hp0 (le_trans hp0 hX)
  have hprod := mul_le_mul hfirst hsecond
    (mul_nonneg hp0 hp0) (le_trans (mul_nonneg hp0 hp0) hfirst)
  calc
    p ^ 4 / 16 = ((p / 2) * (p / 2)) * ((p / 2) * (p / 2)) := by ring
    _ <= ((p - offset e f) * (p + 1 - a)) * ((p - x) * (p - y)) := hprod
    _ = denominator p a e f x y := by unfold denominator; ring

theorem carrier_defect_bound
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |carrier p a e f x y - 1| <= (128 * |a| + 896) / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hpne : Not (p = 0) := ne_of_gt hp0
  have hD := denominator_lower p a e f x y hp ha he hf hx hy
  have hDpos : 0 < denominator p a e f x y :=
    lt_of_lt_of_le (by positivity) hD
  have hDne := ne_of_gt hDpos
  have heq : carrier p a e f x y - 1 =
      (numerator p a e f x y - denominator p a e f x y) /
        denominator p a e f x y := by
    unfold carrier
    field_simp [hDne, hpne]
  rw [heq, abs_div, abs_of_pos hDpos]
  have hnonneg : 0 <= (128 * |a| + 896) / p ^ 2 := by positivity
  have hineq : |numerator p a e f x y - denominator p a e f x y| <=
      ((128 * |a| + 896) / p ^ 2) * denominator p a e f x y := by
    calc
      |numerator p a e f x y - denominator p a e f x y| <=
        (8 * |a| + 56) * p ^ 2 :=
        numerator_sub_denominator_bound p a e f x y hp ha he hf hx hy
      _ = ((128 * |a| + 896) / p ^ 2) * (p ^ 4 / 16) := by
        field_simp [hDne, hpne]
        <;> ring
      _ <= _ := mul_le_mul_of_nonneg_left hD hnonneg

  calc
    _ <= (((128 * |a| + 896) / p ^ 2) * denominator p a e f x y) /
        denominator p a e f x y :=
      div_le_div_of_nonneg_right hineq (le_of_lt hDpos)
    _ = _ := by field_simp [hDne]

theorem carrier_pos
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    0 < carrier p a e f x y := by
  have hZ : correction e f x y <= 8 := by
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [correction]
  have hfx : f * x <= 1 := by
    rcases hf with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num
  have hey : e * y <= 1 := by
    rcases he with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
  have hU : 0 < p + 1 - a - correction e f x y := by
    linarith [le_abs_self a]
  have hN : 0 < numerator p a e f x y := by
    unfold numerator
    exact mul_pos (mul_pos (mul_pos hU (by linarith)) (by linarith)) (by linarith)
  have hD := denominator_lower p a e f x y hp ha he hf hx hy
  have hp0 : 0 < p := by linarith
  have hDpos : 0 < denominator p a e f x y :=
    lt_of_lt_of_le (by positivity) hD
  exact div_pos hN hDpos

theorem carrier_hasse_defect
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= 2 * Real.sqrt p)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |carrier p a e f x y - 1| <= 512 / (p * Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hpne : Not (p = 0) := ne_of_gt hp0
  have hr0 := Real.sqrt_nonneg p
  have hr2 := Real.sq_sqrt (le_of_lt hp0)
  have hr4 : 4 <= Real.sqrt p := by nlinarith
  have hrpos : 0 < Real.sqrt p := by linarith
  have hrne := ne_of_gt hrpos
  have hrmul := mul_nonneg (sub_nonneg.mpr hr4) hr0
  have hahalf : |a| <= p / 2 := by nlinarith
  have hnum : (256 * Real.sqrt p + 896) * Real.sqrt p <= 512 * p := by
    nlinarith
  calc
    |carrier p a e f x y - 1| <= (128 * |a| + 896) / p ^ 2 :=
      carrier_defect_bound p a e f x y hp hahalf he hf hx hy
    _ <= (256 * Real.sqrt p + 896) / p ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = ((256 * Real.sqrt p + 896) * Real.sqrt p) /
        (p ^ 2 * Real.sqrt p) := by field_simp [hpne, hrne]
    _ <= (512 * p) / (p ^ 2 * Real.sqrt p) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 512 / (p * Real.sqrt p) := by field_simp [hpne, hrne]

theorem refined_numerator_bound
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (hasq : a ^ 2 <= 4 * p)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |(numerator p a e f x y - denominator p a e f x y) * p ^ 2 +
        correction e f x y * a * denominator p a e f x y| <=
      1024 * p ^ 4 := by
  have hp0 : 0 <= p := by linarith
  have hp1 : 1 <= p := by linarith
  have haU : a <= p / 2 := le_trans (le_abs_self a) ha
  have haL : -p / 2 <= a := by linarith [neg_le_abs a]
  have hUp := mul_le_mul_of_nonneg_right haU hp0
  have hLp := mul_le_mul_of_nonneg_right haL hp0
  have hUp2 := mul_le_mul_of_nonneg_right haU (pow_nonneg hp0 2)
  have hLp2 := mul_le_mul_of_nonneg_right haL (pow_nonneg hp0 2)
  have hUp3 := mul_le_mul_of_nonneg_right haU (pow_nonneg hp0 3)
  have hLp3 := mul_le_mul_of_nonneg_right haL (pow_nonneg hp0 3)
  have hSqP := mul_le_mul_of_nonneg_right hasq hp0
  have hSqP2 := mul_le_mul_of_nonneg_right hasq (pow_nonneg hp0 2)
  have hSqP3 := mul_le_mul_of_nonneg_right hasq (pow_nonneg hp0 3)
  have hSqP0 := mul_nonneg (sq_nonneg a) hp0
  have hSqP20 := mul_nonneg (sq_nonneg a) (pow_nonneg hp0 2)
  have hSqP30 := mul_nonneg (sq_nonneg a) (pow_nonneg hp0 3)
  have hpStep1 := mul_nonneg (sub_nonneg.mpr hp1) hp0
  have hpStep2 := mul_nonneg (sub_nonneg.mpr hp1) (pow_nonneg hp0 2)
  have hpStep3 := mul_nonneg (sub_nonneg.mpr hp1) (pow_nonneg hp0 3)
  rw [abs_le]
  constructor <;>
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [numerator, denominator, correction, offset] <;>
    ring_nf at * <;>
    linarith only [hp, hp0, hp1, haU, haL, hasq,
      hUp, hLp, hUp2, hLp2, hUp3, hLp3,
      hSqP, hSqP2, hSqP3, hSqP0, hSqP20, hSqP30,
      hpStep1, hpStep2, hpStep3, sq_nonneg a, sq_nonneg p]

theorem carrier_refined_defect
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (hasq : a ^ 2 <= 4 * p)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    |carrier p a e f x y - 1 + correction e f x y * a / p ^ 2| <=
      16384 / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hpne := ne_of_gt hp0
  have hD := denominator_lower p a e f x y hp ha he hf hx hy
  have hDpos : 0 < denominator p a e f x y :=
    lt_of_lt_of_le (by positivity) hD
  have hDne := ne_of_gt hDpos
  have heq : carrier p a e f x y - 1 + correction e f x y * a / p ^ 2 =
      ((numerator p a e f x y - denominator p a e f x y) * p ^ 2 +
        correction e f x y * a * denominator p a e f x y) /
          (denominator p a e f x y * p ^ 2) := by
    unfold carrier
    field_simp [hpne, hDne]
    <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hDpos (sq_pos_of_ne_zero hpne))]
  have hineq :
      |(numerator p a e f x y - denominator p a e f x y) * p ^ 2 +
        correction e f x y * a * denominator p a e f x y| <=
        (16384 / p ^ 2) * (denominator p a e f x y * p ^ 2) := by
    calc
      _ <= 1024 * p ^ 4 :=
        refined_numerator_bound p a e f x y hp ha hasq he hf hx hy
      _ = (16384 : Real) * (p ^ 4 / 16) := by ring
      _ <= 16384 * denominator p a e f x y :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = _ := by field_simp [hpne]
  calc
    _ <= ((16384 / p ^ 2) * (denominator p a e f x y * p ^ 2)) /
        (denominator p a e f x y * p ^ 2) :=
      div_le_div_of_nonneg_right hineq (by positivity)
    _ = _ := by field_simp [hpne, hDne]

def ellipticFactor (p a : Real) : Real := (p + 1 - a) / p

def dirichletFactor (p e f x y : Real) : Real :=
  p * (p - x) * (p - y) / ((p - 1) * (p - f * x) * (p - e * y))

theorem rational_factorization
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    (p + 1 - a - correction e f x y) / (p - offset e f) =
      ellipticFactor p a * dirichletFactor p e f x y * carrier p a e f x y := by
  have hp0 : 0 < p := by linarith
  have hpne := ne_of_gt hp0
  have hD := denominator_lower p a e f x y hp ha he hf hx hy
  have hDpos : 0 < denominator p a e f x y :=
    lt_of_lt_of_le (by positivity) hD
  have hDne := ne_of_gt hDpos
  have hpd : Not (p - offset e f = 0) := by
    intro hz
    apply hDne
    simp only [denominator, hz, zero_mul]
  have hpa : Not (p + 1 - a = 0) := by
    intro hz
    apply hDne
    simp only [denominator, hz, mul_zero, zero_mul]
  have hpx : Not (p - x = 0) := by
    intro hz
    apply hDne
    simp only [denominator, hz, mul_zero, zero_mul]
  have hpy : Not (p - y = 0) := by
    intro hz
    apply hDne
    simp only [denominator, hz, mul_zero]
  have hfx : f * x <= 1 := by
    rcases hf with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num
  have hey : e * y <= 1 := by
    rcases he with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
  have hp1 : Not (p - 1 = 0) := ne_of_gt (by linarith)
  have hpfx : Not (p - f * x = 0) := ne_of_gt (by linarith)
  have hpey : Not (p - e * y = 0) := ne_of_gt (by linarith)
  have hCne : Not ((p - 1) * (p - f * x) * (p - e * y) = 0) :=
    mul_ne_zero (mul_ne_zero hp1 hpfx) hpey
  have hnum : numerator p a e f x y =
      (p + 1 - a - correction e f x y) *
        ((p - 1) * (p - f * x) * (p - e * y)) := by
    unfold numerator
    ring
  unfold ellipticFactor dirichletFactor carrier
  rw [hnum]
  unfold denominator
  generalize hCdef : (p - 1) * (p - f * x) * (p - e * y) = C at *
  field_simp [hpne, hpd, hpa, hpx, hpy, hCne]
  <;> ring

theorem reference_pos
    (p a e f x y : Real) (hp : 16 <= p) (ha : |a| <= p / 2)
    (he : e = 1 \/ e = -1) (hf : f = 1 \/ f = -1)
    (hx : x = 1 \/ x = -1) (hy : y = 1 \/ y = -1) :
    0 < ellipticFactor p a * dirichletFactor p e f x y := by
  have hp0 : 0 < p := by linarith
  have hx1 : x <= 1 := by rcases hx with rfl | rfl <;> norm_num
  have hy1 : y <= 1 := by rcases hy with rfl | rfl <;> norm_num
  have hfx : f * x <= 1 := by
    rcases hf with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num
  have hey : e * y <= 1 := by
    rcases he with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
  have hA : 0 < p + 1 - a := by linarith [le_abs_self a]
  have hX : 0 < p - x := by linarith
  have hY : 0 < p - y := by linarith
  have h1 : 0 < p - 1 := by linarith
  have hFX : 0 < p - f * x := by linarith
  have hEY : 0 < p - e * y := by linarith
  unfold ellipticFactor dirichletFactor
  positivity

end FiniteField.QuadraticPairEuler
