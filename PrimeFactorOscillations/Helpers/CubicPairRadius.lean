/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes

/-!
# Uniform scale differences for cubic Poisson kernels

The lattice estimate is uniform over all coefficient functions bounded by one.
Only explicit finite Schwartz seminorms enter the constant. This is an
analytic input; it does not assert a zero-free region.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CubicPairRadius
open OAI

def radiusTerm (W : SchwartzMap Real Complex) (q t : Real) : Complex :=
  W (q / t ^ 2) / (t : Complex)

def radiusDeriv (W : SchwartzMap Real Complex) (q t : Real) : Complex :=
  (-W (q / t ^ 2) -
    ((2 * (q / t ^ 2) : Real) : Complex) * deriv W (q / t ^ 2)) /
      ((t ^ 2 : Real) : Complex)

theorem radiusTerm_hasDerivAt (W : SchwartzMap Real Complex)
    (q t : Real) (ht : Not (t = 0)) :
    HasDerivAt (radiusTerm W q) (radiusDeriv W q t) t := by
  have harg := (hasDerivAt_const t q).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht)
  have hw := (W.hasDerivAt (q / t ^ 2)).scomp t harg
  have htc : Not ((t : Complex) = 0) := by exact_mod_cast ht
  have hh := hw.div (hasDerivAt_id t).ofReal_comp htc
  convert hh using 1 <;> dsimp [radiusTerm, radiusDeriv] <;>
    push_cast <;> try field_simp <;> ring
  all_goals rfl

theorem radiusDeriv_weighted_bound (W : SchwartzMap Real Complex)
    (C X q t : Real) (hC : 0 <= C) (hX : 0 < X) (hq : 0 <= q)
    (ht : X <= t) (ht2 : t <= 2 * X)
    (hW : forall y : Real, 0 <= y ->
      (1 + y) ^ 2 *
        norm (-W y - ((2 * y : Real) : Complex) * deriv W y) <= C) :
    (1 + q / (4 * X ^ 2)) ^ 2 * norm (radiusDeriv W q t) <= C / X ^ 2 := by
  have ht0 : 0 < t := hX.trans_le ht
  have hts : 0 < t ^ 2 := sq_pos_of_pos ht0
  have hxs : 0 < X ^ 2 := sq_pos_of_pos hX
  have hsmall : t ^ 2 <= 4 * X ^ 2 := by nlinarith
  have hlarge : X ^ 2 <= t ^ 2 := by nlinarith
  have harg : q / (4 * X ^ 2) <= q / t ^ 2 :=
    div_le_div_of_nonneg_left hq hts hsmall
  have hA : (1 + q / (4 * X ^ 2)) ^ 2 <= (1 + q / t ^ 2) ^ 2 :=
    by
      have hn : 0 <= q / (4 * X ^ 2) := by positivity
      have hm := mul_nonneg (sub_nonneg.mpr harg)
        (show 0 <= 2 + q / t ^ 2 + q / (4 * X ^ 2) by positivity)
      nlinarith
  have hB := (mul_le_mul_of_nonneg_right hA
    (norm_nonneg (-W (q / t ^ 2) -
      ((2 * (q / t ^ 2) : Real) : Complex) * deriv W (q / t ^ 2)))).trans
        (hW (q / t ^ 2) (div_nonneg hq hts.le))
  calc
    _ = ((1 + q / (4 * X ^ 2)) ^ 2 *
        norm (-W (q / t ^ 2) -
          ((2 * (q / t ^ 2) : Real) : Complex) * deriv W (q / t ^ 2))) /
            t ^ 2 := by
      rw [radiusDeriv, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hts.le, mul_div_assoc]
    _ <= C / t ^ 2 := div_le_div_of_nonneg_right hB hts.le
    _ <= C / X ^ 2 := div_le_div_of_nonneg_left hC hxs hlarge

theorem radiusTerm_weighted_lipschitz (W : SchwartzMap Real Complex)
    (C X q t u : Real) (hC : 0 <= C) (hX : 0 < X) (hq : 0 <= q)
    (ht : X <= t) (ht2 : t <= 2 * X) (hu : X <= u) (hu2 : u <= 2 * X)
    (hW : forall y : Real, 0 <= y ->
      (1 + y) ^ 2 *
        norm (-W y - ((2 * y : Real) : Complex) * deriv W y) <= C) :
    (1 + q / (4 * X ^ 2)) ^ 2 *
        norm (radiusTerm W q t - radiusTerm W q u) <=
      (C / X ^ 2) * abs (t - u) := by
  let A : Real := (1 + q / (4 * X ^ 2)) ^ 2
  have hA : 0 <= A := by positivity
  let f : Real -> Complex := fun r => HSMul.hSMul A (radiusTerm W q r)
  have hf (r : Real) (hr : Membership.mem (Set.Icc X (2 * X)) r) :
      HasDerivAt f (HSMul.hSMul A (radiusDeriv W q r)) r := by
    have hr0 : Not (r = 0) := ne_of_gt (hX.trans_le hr.1)
    exact (radiusTerm_hasDerivAt W q r hr0).const_smul A
  have hb (r : Real) (hr : Membership.mem (Set.Icc X (2 * X)) r) :
      norm (deriv f r) <= C / X ^ 2 := by
    rw [(hf r hr).deriv, _root_.norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hA]
    exact radiusDeriv_weighted_bound W C X q r hC hX hq hr.1 hr.2 hW
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (hf r hr).differentiableAt) hb (convex_Icc X (2 * X))
      (And.intro hu hu2) (And.intro ht ht2)
  change norm (HSMul.hSMul A (radiusTerm W q t) -
    HSMul.hSMul A (radiusTerm W q u)) <= _ at hh
  rw [<- _root_.smul_sub, _root_.norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hA, Real.norm_eq_abs] at hh
  exact hh

def windowSize0 (W : SchwartzMap Real Complex) : Real :=
  abs (SchwartzMap.seminorm Real 0 0 W) +
    2 * abs (SchwartzMap.seminorm Real 1 0 W) +
      abs (SchwartzMap.seminorm Real 2 0 W)

def windowSize1 (W : SchwartzMap Real Complex) : Real :=
  windowSize0 W + 2 * abs (SchwartzMap.seminorm Real 1 1 W) +
    4 * abs (SchwartzMap.seminorm Real 2 1 W) +
      2 * abs (SchwartzMap.seminorm Real 3 1 W)

theorem windowSize0_nonneg (W : SchwartzMap Real Complex) : 0 <= windowSize0 W := by
  unfold windowSize0
  positivity

theorem windowSize1_nonneg (W : SchwartzMap Real Complex) : 0 <= windowSize1 W := by
  unfold windowSize1 windowSize0
  positivity

theorem window_bound0 (W : SchwartzMap Real Complex) (u : Real) (hu : 0 <= u) :
    (1 + u) ^ 2 * norm (W u) <= windowSize0 W := by
  have h0 := (SchwartzMap.norm_le_seminorm Real W u).trans
    (le_abs_self (SchwartzMap.seminorm Real 0 0 W))
  have h1 := (SchwartzMap.norm_pow_mul_le_seminorm Real W 1 u).trans
    (le_abs_self (SchwartzMap.seminorm Real 1 0 W))
  have h2 := (SchwartzMap.norm_pow_mul_le_seminorm Real W 2 u).trans
    (le_abs_self (SchwartzMap.seminorm Real 2 0 W))
  simp only [Real.norm_eq_abs, abs_of_nonneg hu, pow_one] at h1 h2
  unfold windowSize0
  nlinarith only [h0, h1, h2]

theorem window_bound1 (W : SchwartzMap Real Complex) (u : Real) (hu : 0 <= u) :
    (1 + u) ^ 2 *
      norm (-W u - ((2 * u : Real) : Complex) * deriv W u) <= windowSize1 W := by
  have h0 := window_bound0 W u hu
  have h1 := (SchwartzMap.le_seminorm' Real 1 1 W u).trans
    (le_abs_self (SchwartzMap.seminorm Real 1 1 W))
  have h2 := (SchwartzMap.le_seminorm' Real 2 1 W u).trans
    (le_abs_self (SchwartzMap.seminorm Real 2 1 W))
  have h3 := (SchwartzMap.le_seminorm' Real 3 1 W u).trans
    (le_abs_self (SchwartzMap.seminorm Real 3 1 W))
  simp only [iteratedDeriv_one, abs_of_nonneg hu, pow_one] at h1 h2 h3
  have hN := norm_sub_le (-W u) (((2 * u : Real) : Complex) * deriv W u)
  norm_num only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu] at hN
  have hNm := mul_le_mul_of_nonneg_left hN (sq_nonneg (1 + u))
  unfold windowSize1
  nlinarith only [h0, h1, h2, h3, hNm]

set_option maxHeartbeats 800000 in
theorem scaled_all_cauchy_mass (K : Real) (hK : 0 < K) :
    K * (tsum fun z : ActualEisensteinCubic.O =>
      Inv.inv ((1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2)) <=
        K + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant := by
  classical
  let f : ActualEisensteinCubic.O -> Real := fun z =>
    Inv.inv ((1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2)
  have hs : Summable f :=
    EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable K hK
  have he :
      1 + (tsum fun z : {z : ActualEisensteinCubic.O // Not (z = 0)} => f z.val) =
        tsum f := by
    let e : Equiv
        {z : ActualEisensteinCubic.O //
          Not (Membership.mem ({0} : Finset ActualEisensteinCubic.O) z)}
        {z : ActualEisensteinCubic.O // Not (z = 0)} :=
      Equiv.subtypeEquivRight (fun _ => Finset.notMem_singleton)
    have hindex :
        (tsum fun z : {z : ActualEisensteinCubic.O //
          Not (Membership.mem ({0} : Finset ActualEisensteinCubic.O) z)} => f z.val) =
        (tsum fun z : {z : ActualEisensteinCubic.O // Not (z = 0)} => f z.val) :=
      Equiv.tsum_eq e (fun z => f z.val)
    have hh := hs.sum_add_tsum_subtype_compl ({0} : Finset ActualEisensteinCubic.O)
    have hf0 : f (0 : ActualEisensteinCubic.O) = 1 := by norm_num [f]
    rw [Finset.sum_singleton, hf0, hindex] at hh
    exact hh
  have hn := EisensteinSchwartzPoisson.scaled_cauchy_nonzero_mass K hK
  change K * tsum f <= _
  rw [<- he, mul_add, mul_one]
  simpa only [f, add_comm] using add_le_add_left hn K

theorem dominated_lattice_sum (f : ActualEisensteinCubic.O -> Complex)
    (K B : Real) (hK : 0 < K) (hB : 0 <= B)
    (hf : forall z : ActualEisensteinCubic.O,
      (1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2 * norm (f z) <= B) :
    Summable f /\
      K * norm (tsum f) <=
        B * (K + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) := by
  let g : ActualEisensteinCubic.O -> Real := fun z =>
    Inv.inv ((1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2)
  have hs : Summable g :=
    EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable K hK
  have hp (z : ActualEisensteinCubic.O) : norm (f z) <= B * g z := by
    let A : Real := (1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2
    have hA : 0 < A := by dsimp [A]; positivity
    have hc : B = A * (B * g z) := by
      change B = A * (B / A)
      field_simp [ne_of_gt hA]
    apply le_of_not_gt
    intro h
    have hm := mul_lt_mul_of_pos_left h hA
    rw [<- hc] at hm
    exact not_lt_of_ge (hf z) hm
  have hsf : Summable (fun z => norm (f z)) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp (hs.mul_left B)
  refine And.intro hsf.of_norm ?_
  have hn : norm (tsum f) <= B * tsum g := by
    calc
      _ <= tsum (fun z => norm (f z)) := norm_tsum_le_tsum_norm hsf
      _ <= tsum (fun z => B * g z) := hsf.tsum_le_tsum hp (hs.mul_left B)
      _ = _ := tsum_mul_left
  calc
    _ <= K * (B * tsum g) := mul_le_mul_of_nonneg_left hn hK.le
    _ = B * (K * tsum g) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left (scaled_all_cauchy_mass K hK) hB



def latticeScaleDifference
    (c : ActualEisensteinCubic.O -> Complex) (W : SchwartzMap Real Complex)
    (t u : Real) : Complex :=
  tsum fun z => c z *
    (radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t -
      radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) u)

theorem latticeScaleDifference_bound
    (c : ActualEisensteinCubic.O -> Complex) (hc : forall z, norm (c z) <= 1)
    (W : SchwartzMap Real Complex) (X t u : Real) (hX : 1 <= X)
    (ht : X <= t) (ht2 : t <= 2 * X) (hu : X <= u) (hu2 : u <= 2 * X) :
    norm (latticeScaleDifference c W t u) <=
      4 * windowSize1 W *
        (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) * abs (t - u) := by
  have hX0 : 0 < X := by linarith
  have hC : 0 <= windowSize1 W := windowSize1_nonneg W
  let K : Real := 1 / (4 * X ^ 2)
  let B : Real := (windowSize1 W / X ^ 2) * abs (t - u)
  let f : ActualEisensteinCubic.O -> Complex := fun z => c z *
    (radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t -
      radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) u)
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  have hp (z : ActualEisensteinCubic.O) :
      (1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2 * norm (f z) <= B := by
    have hw := radiusTerm_weighted_lipschitz W (windowSize1 W) X
      (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t u hC hX0 (sq_nonneg _)
        ht ht2 hu hu2 (window_bound1 W)
    have hn : norm (f z) <=
        norm (radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t -
          radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) u) := by
      dsimp [f]
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hc z) (norm_nonneg _)
    calc
      _ <= (1 + K * norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) ^ 2 *
        norm (radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t -
          radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) u) :=
            mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ <= B := by
        convert hw using 1
        dsimp [K, B]
        ring
  have hb := (dominated_lattice_sum f K B hK hB hp).2
  have hKI : K * (4 * X ^ 2) = 1 := by
    dsimp [K]
    field_simp [ne_of_gt hX0]
  have hK1 : K <= 1 := by
    have hXX : 1 <= X ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hXX hK.le
    nlinarith
  have hB4 : B = 4 * windowSize1 W * K * abs (t - u) := by
    dsimp [B, K]
    ring
  have hFinal :
      K * norm (latticeScaleDifference c W t u) <=
        K * (4 * windowSize1 W *
          (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) * abs (t - u)) := by
    calc
      _ <= B * (K + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) := hb
      _ = (4 * windowSize1 W * K * abs (t - u)) *
          (K + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) := by rw [hB4]
      _ <= (4 * windowSize1 W * K * abs (t - u)) *
          (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) :=
        mul_le_mul_of_nonneg_left
          (show K + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant <=
            1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant by linarith)
            (by positivity)
      _ = _ := by ring
  apply le_of_not_gt
  intro h
  exact not_lt_of_ge hFinal (mul_lt_mul_of_pos_left h hK)

def radiusKernel (c : ActualEisensteinCubic.O -> Complex)
    (W : SchwartzMap Real Complex) (t : Real) : Complex :=
  tsum fun z => c z * radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t

theorem radiusTerm_summable
    (c : ActualEisensteinCubic.O -> Complex) (hc : forall z, norm (c z) <= 1)
    (W : SchwartzMap Real Complex) (t : Real) (ht : 0 < t) :
    Summable (fun z => c z * radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t) := by
  let K : Real := 1 / t ^ 2
  let B : Real := windowSize0 W / t
  let f : ActualEisensteinCubic.O -> Complex := fun z =>
    c z * radiusTerm W (norm (ConcreteTraceCRT.eisEmbedding z) ^ 2) t
  have hC : 0 <= windowSize0 W := windowSize0_nonneg W
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  apply (dominated_lattice_sum f K B hK hB ?_).1
  intro z
  let q : Real := norm (ConcreteTraceCRT.eisEmbedding z) ^ 2
  have hq : 0 <= q := sq_nonneg _
  have hn : norm (f z) <= norm (W (q / t ^ 2)) / t := by
    dsimp [f, radiusTerm, q]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hc z) (div_nonneg (norm_nonneg _) ht.le)
  have he : K * q = q / t ^ 2 := by dsimp [K]; ring
  change (1 + K * q) ^ 2 * norm (f z) <= B
  rw [he]
  calc
    _ <= (1 + q / t ^ 2) ^ 2 * (norm (W (q / t ^ 2)) / t) :=
      mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ = ((1 + q / t ^ 2) ^ 2 * norm (W (q / t ^ 2))) / t := by ring
    _ <= B := div_le_div_of_nonneg_right (window_bound0 W _ (by positivity)) ht.le

theorem radiusKernel_difference_bound
    (c : ActualEisensteinCubic.O -> Complex) (hc : forall z, norm (c z) <= 1)
    (W : SchwartzMap Real Complex) (X t u : Real) (hX : 1 <= X)
    (ht : X <= t) (ht2 : t <= 2 * X) (hu : X <= u) (hu2 : u <= 2 * X) :
    norm (radiusKernel c W t - radiusKernel c W u) <=
      4 * windowSize1 W *
        (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant) * abs (t - u) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : (0 : Real) < X) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith : (0 : Real) < X) hu
  have hst := radiusTerm_summable c hc W t ht0
  have hsu := radiusTerm_summable c hc W u hu0
  have he : latticeScaleDifference c W t u = radiusKernel c W t - radiusKernel c W u := by
    unfold latticeScaleDifference radiusKernel
    simp_rw [mul_sub]
    exact hst.tsum_sub hsu
  rw [<- he]
  exact latticeScaleDifference_bound c hc W X t u hX ht ht2 hu hu2

end PrimeFactorOscillations.CubicPairRadius
