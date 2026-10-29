/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.CarmichaelNativeHyperbola
import PrimeFactorOscillations.Assembly.CarmichaelRamanujanFrequency

/-!
# Signed coprime Euler coordinates

The actual rational coprime unit has local factor 1-a*u-a*v.
On a conjugate pair of Mellin coordinates its diagonal Euler correction is
real and positive in the stated domain. The same-zero correction satisfies
the reverse of a Gram comparison, strictly at a nonreal local phase.
Every reciprocal denominator is retained.

These are signed-coordinate estimates. They do not assert a bound for the
Mobius high packet, a Mellin contour passage, or an improved zero-free strip.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelCoprimeSignedWave

open scoped BigOperators Classical

def localDiagonal (a : Real) (z : Complex) : Real :=
  (1 - 2 * a * z.re) / norm (1 - z) ^ 2

def localOffDiagonal (a : Real) (z : Complex) : Complex :=
  (1 - ((2 * a : Real) : Complex) * z) / (1 - z) ^ 2

/-- The full local quotient, before any norm comparison. -/
theorem local_signed_factorization (a : Real) (u v : Complex) :
    1 - (a : Complex) * u - (a : Complex) * v =
      (1 - u) * (1 - v) -
        (u * v + ((a - 1 : Real) : Complex) * (u + v)) := by
  push_cast
  ring

theorem numerator_norm_square (a : Real) (z : Complex) :
    norm (1 - ((2 * a : Real) : Complex) * z) ^ 2 =
      (1 - 2 * a * z.re) ^ 2 + (2 * a * z.im) ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The strict gap is an explicit phase square, with both denominators kept. -/
theorem local_gap_square (a : Real) (z : Complex) :
    norm (localOffDiagonal a z) ^ 2 =
      (localDiagonal a z) ^ 2 +
        (2 * a * z.im / norm (1 - z) ^ 2) ^ 2 := by
  unfold localOffDiagonal localDiagonal
  rw [norm_div, norm_pow]
  simp only [div_pow]
  rw [numerator_norm_square]
  ring

theorem local_reverse_comparison (a : Real) (z : Complex)
    (_h : 0 <= localDiagonal a z) :
    localDiagonal a z <= norm (localOffDiagonal a z) := by
  have he := local_gap_square a z
  have hn := norm_nonneg (localOffDiagonal a z)
  nlinarith [sq_nonneg (2 * a * z.im / norm (1 - z) ^ 2)]

theorem local_reverse_comparison_strict (a : Real) (z : Complex)
    (h : 0 < localDiagonal a z)
    (hPhase : Not (a * z.im = 0)) :
    localDiagonal a z < norm (localOffDiagonal a z) := by
  have hd : Not (norm (1 - z) = 0) := by
    intro he
    have hz : localDiagonal a z = 0 := by simp [localDiagonal, he]
    linarith
  have hn : Not (2 * a * z.im = 0) := by
    simpa only [mul_assoc] using
      (mul_ne_zero (by norm_num : Not ((2 : Real) = 0)) hPhase)
  have hq : Not (2 * a * z.im / norm (1 - z) ^ 2 = 0) :=
    div_ne_zero hn (pow_ne_zero 2 hd)
  have he := local_gap_square a z
  have hp : 0 < (2 * a * z.im / norm (1 - z) ^ 2) ^ 2 :=
    sq_pos_of_ne_zero hq
  nlinarith [norm_nonneg (localOffDiagonal a z)]

theorem localDiagonal_pos_of_bounds (a : Real) (z : Complex)
    (ha : 0 <= a) (haUpper : a <= 5 / 4)
    (hz : norm z <= 3 / 10) :
    0 < localDiagonal a z := by
  have hre : z.re <= 3 / 10 := (Complex.re_le_norm z).trans hz
  have hm := mul_le_mul_of_nonneg_left hre ha
  have hm2 := mul_le_mul_of_nonneg_right haUpper
    (by norm_num : (0 : Real) <= 3 / 10)
  have hnum : 0 < 1 - 2 * a * z.re := by nlinarith
  have hne : Not (1 - z = 0) := by
    intro he
    have heq : z = 1 := (sub_eq_zero.mp he).symm
    rw [heq, norm_one] at hz
    norm_num at hz
  have hp : 0 < norm (1 - z) := norm_pos_iff.mpr hne
  exact div_pos hnum (sq_pos_of_pos hp)

theorem finite_product_reverse_comparison {I : Type*}
    (P : Finset I) (a : I -> Real) (z : I -> Complex)
    (h : forall i, Membership.mem P i -> 0 <= localDiagonal (a i) (z i)) :
    P.prod (fun i => localDiagonal (a i) (z i)) <=
      norm (P.prod (fun i => localOffDiagonal (a i) (z i))) := by
  classical
  revert h
  induction P using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert i P hi ih =>
    intro h
    have hP : forall j, Membership.mem P j ->
        0 <= localDiagonal (a j) (z j) := by
      intro j hj
      exact h j (Finset.mem_insert_of_mem hj)
    have hProd : 0 <= P.prod (fun j => localDiagonal (a j) (z j)) :=
      Finset.prod_nonneg hP
    rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul]
    exact mul_le_mul
      (local_reverse_comparison (a i) (z i) (h i (Finset.mem_insert_self _ _)))
      (ih hP) hProd (norm_nonneg _)

theorem finite_product_reverse_comparison_strict {I : Type*}
    (P : Finset I) (a : I -> Real) (z : I -> Complex)
    (h : forall i, Membership.mem P i -> 0 < localDiagonal (a i) (z i))
    (p : I) (hp : Membership.mem P p)
    (hPhase : Not (a p * (z p).im = 0)) :
    P.prod (fun i => localDiagonal (a i) (z i)) <
      norm (P.prod (fun i => localOffDiagonal (a i) (z i))) := by
  have hePos : 0 < (P.erase p).prod (fun i => localDiagonal (a i) (z i)) := by
    apply Finset.prod_pos
    intro i hi
    exact h i (Finset.mem_of_mem_erase hi)
  have heLe :=
    finite_product_reverse_comparison (P.erase p) a z
      (fun i hi => (h i (Finset.mem_of_mem_erase hi)).le)
  rw [norm_prod] at heLe
  rw [norm_prod,
    <- Finset.mul_prod_erase P (fun i => localDiagonal (a i) (z i)) hp,
    <- Finset.mul_prod_erase P (fun i => norm (localOffDiagonal (a i) (z i))) hp]
  calc
    _ < norm (localOffDiagonal (a p) (z p)) *
        (P.erase p).prod (fun i => localDiagonal (a i) (z i)) :=
      mul_lt_mul_of_pos_right
        (local_reverse_comparison_strict (a p) (z p) (h p hp) hPhase) hePos
    _ <= _ := mul_le_mul_of_nonneg_left heLe (norm_nonneg _)

def cancellingPhase (c : Complex) : Complex :=
  -star c / (norm c : Complex)

theorem cancellingPhase_properties (c : Complex) (hc : Not (c = 0)) :
    norm (cancellingPhase c) = 1 /\
      (c * cancellingPhase c).re = -norm c := by
  have hn : Not (norm c = 0) := by
    intro h
    exact hc (norm_eq_zero.mp h)
  have hnC : Not ((norm c : Complex) = 0) := by exact_mod_cast hn
  have hNorm : norm (cancellingPhase c) = 1 := by
    unfold cancellingPhase
    rw [norm_div, norm_neg, norm_star]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c)]
    exact div_self hn
  have hcc : c * star c = (((norm c) ^ 2 : Real) : Complex) := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj c
  have hValue : c * cancellingPhase c = -(norm c : Complex) := by
    unfold cancellingPhase
    calc
      _ = -(c * star c) / (norm c : Complex) := by ring
      _ = -(((norm c) ^ 2 : Real) : Complex) / (norm c : Complex) := by rw [hcc]
      _ = -(norm c : Complex) := by
        push_cast
        field_simp
  exact And.intro hNorm (by rw [hValue]; simp)

def compensatedResponse (d : Real) (c u w : Complex) : Real :=
  2 * d * norm (1 - w) ^ 2 + 2 * (c * u * (1 - w) ^ 2).re

theorem norm_one_sub_square (w : Complex) :
    norm (1 - w) ^ 2 = 1 - 2 * w.re + norm w ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [<- Complex.normSq_eq_norm_sq w, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- AA, AB, BA and BB are kept before the damping remainder is estimated. -/
theorem compensatedResponse_expand (d : Real) (c u w : Complex) :
    compensatedResponse d c u w =
      2 * d + 2 * (c * u).re -
        4 * d * w.re - 4 * (c * u * w).re +
        2 * d * norm w ^ 2 + 2 * (c * u * w ^ 2).re := by
  unfold compensatedResponse
  rw [norm_one_sub_square]
  have he : c * u * (1 - w) ^ 2 =
      c * u - 2 * (c * u * w) + c * u * w ^ 2 := by ring
  rw [he]
  have hTwo (z : Complex) : (2 * z).re = 2 * z.re := by simp
  simp only [Complex.add_re, Complex.sub_re, hTwo]
  ring

theorem compensatedResponse_zero (d : Real) (c u : Complex) :
    compensatedResponse d c u 0 = 2 * (d + (c * u).re) := by
  simp only [compensatedResponse, sub_zero, norm_one, one_pow, mul_one]
  ring

/-- A norm is used only on the explicit quadratic damping error. -/
theorem damping_remainder_bound (w : Complex) :
    norm ((1 - w) ^ 2 - 1) <= 2 * norm w + norm w ^ 2 := by
  have he : (1 - w) ^ 2 - 1 = -2 * w + w ^ 2 := by ring
  rw [he]
  calc
    _ <= norm (-2 * w) + norm (w ^ 2) := norm_add_le _ _
    _ = _ := by norm_num [norm_mul, norm_pow]

theorem compensatedResponse_upper_remainder (d : Real) (c u w : Complex)
    (hd : 0 <= d) (hu : norm u = 1) :
    compensatedResponse d c u w <= compensatedResponse d c u 0 +
      2 * (d + norm c) * (2 * norm w + norm w ^ 2) := by
  have hr : -norm w <= w.re :=
    (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hReal : norm (1 - w) ^ 2 - 1 <= 2 * norm w + norm w ^ 2 := by
    rw [norm_one_sub_square]
    linarith
  have hComplex :
      (c * u * ((1 - w) ^ 2 - 1)).re <=
        norm c * (2 * norm w + norm w ^ 2) := by
    calc
      _ <= norm (c * u * ((1 - w) ^ 2 - 1)) := Complex.re_le_norm _
      _ = norm c * norm ((1 - w) ^ 2 - 1) := by
        rw [norm_mul, norm_mul, hu, mul_one]
      _ <= _ := mul_le_mul_of_nonneg_left (damping_remainder_bound w) (norm_nonneg c)
  have hRealScaled := mul_le_mul_of_nonneg_left hReal
    (mul_nonneg (by norm_num : (0 : Real) <= 2) hd)
  have he : c * u * (1 - w) ^ 2 =
      c * u + c * u * ((1 - w) ^ 2 - 1) := by ring
  rw [compensatedResponse_zero]
  unfold compensatedResponse
  rw [he, Complex.add_re]
  nlinarith

/-- The selected negative phase survives every sufficiently small complex damping. -/
theorem compensatedResponse_negative (d : Real) (c : Complex)
    (hd : 0 <= d) (hGap : d < norm c) :
    exists u : Complex, norm u = 1 /\
      forall w : Complex, norm w <= 1 ->
        6 * (d + norm c) * norm w <= norm c - d ->
        compensatedResponse d c u w <= -(norm c - d) := by
  have hc : Not (c = 0) := by
    intro h
    rw [h, norm_zero] at hGap
    linarith
  have hPhase := cancellingPhase_properties c hc
  refine Exists.intro (cancellingPhase c) (And.intro hPhase.1 ?_)
  intro w hw hSmall
  have hZero : compensatedResponse d c (cancellingPhase c) 0 =
      -2 * (norm c - d) := by
    rw [compensatedResponse_zero, hPhase.2]
    ring
  have hBound := compensatedResponse_upper_remainder d c (cancellingPhase c) w
    hd hPhase.1
  rw [hZero] at hBound
  have hn := norm_nonneg w
  have hDamp : 2 * norm w + norm w ^ 2 <= 3 * norm w := by nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hDamp
    (mul_nonneg (by norm_num : (0 : Real) <= 2) (add_nonneg hd (norm_nonneg c)))
  nlinarith

/-- Full finite signed Euler products retain a negative compensated phase. -/
theorem finite_product_compensated_negative {I : Type*}
    (P : Finset I) (a : I -> Real) (z : I -> Complex)
    (h : forall i, Membership.mem P i -> 0 < localDiagonal (a i) (z i))
    (p : I) (hp : Membership.mem P p)
    (hPhase : Not (a p * (z p).im = 0)) :
    let d := P.prod (fun i => localDiagonal (a i) (z i))
    let c := P.prod (fun i => localOffDiagonal (a i) (z i))
    exists u : Complex, norm u = 1 /\
      forall w : Complex, norm w <= 1 ->
        6 * (d + norm c) * norm w <= norm c - d ->
        compensatedResponse d c u w <= -(norm c - d) := by
  dsimp only
  apply compensatedResponse_negative
  . apply Finset.prod_nonneg
    intro i hi
    exact (h i hi).le
  . exact finite_product_reverse_comparison_strict P a z h p hp hPhase

end PrimeFactorOscillations.CarmichaelCoprimeSignedWave
