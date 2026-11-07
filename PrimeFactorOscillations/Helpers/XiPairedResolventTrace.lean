/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RiemannXiDivisorStrip
import Mathlib.Topology.Algebra.InfiniteSum.Module
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventKernel
import Robin1984.NicolasLandau.XiZeroConstant

/-!
# The complete reflected xi resolvent trace

Subtracting the Hadamard formulas at opposite horizontal offsets cancels
the common polynomial constant and every reciprocal correction exactly.
The functional equation turns the result into an even-height trace.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984
open BombieriVinogradov.SiegelWalfisz

def xiResolventPoint (r t : Real) : Complex :=
  (1 / 2 : Complex) + (r : Complex) + (t : Complex) * Complex.I

def xiPairedLogTrace (r t : Real) : Real :=
  ((logDeriv riemannXi (xiResolventPoint r t)).re +
    (logDeriv riemannXi (xiResolventPoint r (-t))).re) / 2

theorem xi_genus_summable_of_distance (s : Complex) (delta : Real)
    (hd : 0 < delta)
    (hDist : forall p : RiemannXiDivisorZeroIndex,
      delta <= norm (s - riemannXiDivisorZeroValue p)) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      1 / (s - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p) := by
  let C : Real := norm s * (delta + norm s) / delta
  apply (summable_robinXiZeroWeight.mul_left C).of_norm_bounded
  intro p
  let z := riemannXiDivisorZeroValue p
  have hz : Not (z = 0) := riemannXiDivisorZeroValue_ne_zero p
  have hA : 0 < norm z := norm_pos_iff.mpr hz
  have hB : 0 < norm (s - z) := lt_of_lt_of_le hd (hDist p)
  have hsz : Not (s - z = 0) := norm_pos_iff.mp hB
  have hTriangle : norm z <= norm (s - z) + norm s := by
    calc
      norm z = norm (s - (s - z)) := by congr 1; ring
      _ <= norm s + norm (s - z) := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hAB : norm z * delta <= norm (s - z) * (delta + norm s) := by
    have hh := mul_le_mul_of_nonneg_right hTriangle hd.le
    have hProd := mul_le_mul_of_nonneg_left (hDist p) (norm_nonneg s)
    nlinarith only [hh, hProd]
  have hPacket : 1 / (s - z) + 1 / z = s / (z * (s - z)) := by
    field_simp [hz, hsz]
    ring
  change norm (1 / (s - z) + 1 / z) <= C * (Inv.inv (norm z)) ^ 2
  rw [hPacket, norm_div, norm_mul]
  rw [show C * (Inv.inv (norm z)) ^ 2 = C / (norm z) ^ 2 by
    simp only [div_eq_mul_inv, inv_pow]]
  have hMultiplier :
      0 <= norm s / ((norm z) ^ 2 * norm (s - z) * delta) := by
    exact div_nonneg (norm_nonneg s)
      (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hd.le)
  have hh := mul_le_mul_of_nonneg_left hAB hMultiplier
  convert hh using 1 <;> (try dsimp only [C]) <;>
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hd]

theorem xi_point_genus_summable (r t : Real) (hr : 1 / 2 < r) :
    And
      (Summable (fun p : RiemannXiDivisorZeroIndex =>
        1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))
      (Summable (fun p : RiemannXiDivisorZeroIndex =>
        1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) := by
  have hd : 0 < r - 1 / 2 := by linarith only [hr]
  constructor
  . apply xi_genus_summable_of_distance _ (r - 1 / 2) hd
    intro p
    have hStrip := riemannXiDivisorZeroValue_re_mem_Ioo p
    have hRe : r - 1 / 2 <=
        (xiResolventPoint r t - riemannXiDivisorZeroValue p).re := by
      simp [xiResolventPoint]
      linarith only [hStrip.2]
    exact hRe.trans (Complex.re_le_norm _)
  . apply xi_genus_summable_of_distance _ (r - 1 / 2) hd
    intro p
    have hStrip := riemannXiDivisorZeroValue_re_mem_Ioo p
    have hRe : r - 1 / 2 <=
        -(xiResolventPoint (-r) t - riemannXiDivisorZeroValue p).re := by
      simp [xiResolventPoint]
      linarith only [hStrip.1]
    exact hRe.trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _))

theorem xi_logDeriv_one_sub (s : Complex) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have hOuter : HasDerivAt riemannXi
      (deriv riemannXi (1 - s)) (1 - s) :=
    differentiable_riemannXi.differentiableAt.hasDerivAt
  have hInner : HasDerivAt (fun z : Complex => 1 - z) (-1) s :=
    (hasDerivAt_id s).const_sub 1
  have hRaw := hOuter.comp s hInner
  have hFunction :
      (fun z : Complex => riemannXi (1 - z)) = riemannXi :=
    funext riemannXi_one_sub
  have hDerivative :
      deriv riemannXi s = -deriv riemannXi (1 - s) := by
    have h := hRaw.deriv
    change deriv (fun z : Complex => riemannXi (1 - z)) s =
      deriv riemannXi (1 - s) * (-1) at h
    rw [hFunction] at h
    simpa only [mul_neg_one] using h
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub]
  rw [show deriv riemannXi (1 - s) = -deriv riemannXi s by
    simpa only [neg_neg] using congrArg Neg.neg hDerivative.symm]
  ring

theorem xi_logDeriv_sub_eq_tsum (s z : Complex)
    (hs : forall p : RiemannXiDivisorZeroIndex,
      Not (s = riemannXiDivisorZeroValue p))
    (hz : forall p : RiemannXiDivisorZeroIndex,
      Not (z = riemannXiDivisorZeroValue p))
    (hS : Summable (fun p : RiemannXiDivisorZeroIndex =>
      1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p))
    (hZ : Summable (fun p : RiemannXiDivisorZeroIndex =>
      1 / (z - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p)) :
    logDeriv riemannXi s - logDeriv riemannXi z =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / (s - riemannXiDivisorZeroValue p) -
          1 / (z - riemannXiDivisorZeroValue p)) := by
  choose P hDegree hFactorization using riemannXi_hadamard_factorization_no_monomial
  have hAtS := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    hFactorization hs
  have hAtZ := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    hFactorization hz
  rw [riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero
    hDegree hFactorization s] at hAtS
  rw [riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero
    hDegree hFactorization z] at hAtZ
  calc
    logDeriv riemannXi s - logDeriv riemannXi z =
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          1 / (s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p) -
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          1 / (z - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p) := by
      rw [hAtS, hAtZ]
      ring
    _ = _ := by
      rw [<- hS.tsum_sub hZ]
      apply tsum_congr
      intro p
      ring

theorem xiResolventPoint_away (r t : Real) (hr : 1 / 2 < r)
    (p : RiemannXiDivisorZeroIndex) :
    And (Not (xiResolventPoint r t = riemannXiDivisorZeroValue p))
      (Not (xiResolventPoint (-r) t = riemannXiDivisorZeroValue p)) := by
  have hStrip := riemannXiDivisorZeroValue_re_mem_Ioo p
  constructor
  . intro h
    have hh := congrArg Complex.re h
    simp [xiResolventPoint] at hh
    linarith only [hh, hStrip.2, hr]
  . intro h
    have hh := congrArg Complex.re h
    simp [xiResolventPoint] at hh
    linarith only [hh, hStrip.1, hr]

theorem xiResolventPoint_reflection (r t : Real) :
    xiResolventPoint (-r) t = 1 - xiResolventPoint r (-t) := by
  unfold xiResolventPoint
  push_cast
  ring

theorem xiResolvent_real_difference (r t : Real) (z : Complex) :
    (1 / (xiResolventPoint r t - z) -
      1 / (xiResolventPoint (-r) t - z)).re / 2 =
    pairedResolventMean r (z.re - 1 / 2) (t - z.im) := by
  have h0 : (xiResolventPoint r t - z).re = r - (z.re - 1 / 2) := by
    simp [xiResolventPoint]
    ring
  have h1 : (xiResolventPoint (-r) t - z).re =
      -(r + (z.re - 1 / 2)) := by
    simp [xiResolventPoint]
    ring
  have hi0 : (xiResolventPoint r t - z).im = t - z.im := by
    simp [xiResolventPoint]
  have hi1 : (xiResolventPoint (-r) t - z).im = t - z.im := by
    simp [xiResolventPoint]
  simp only [Complex.sub_re, one_div, Complex.inv_re,
    Complex.normSq_apply, h0, h1, hi0, hi1]
  unfold pairedResolventMean
  ring

theorem xi_paired_resolvent_summable (r t : Real) (hr : 1 / 2 < r) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      pairedResolventMean r
        ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (t - (riemannXiDivisorZeroValue p).im)) := by
  have hs := (xi_point_genus_summable r t hr).1
  have hz := (xi_point_genus_summable r t hr).2
  have hh := (Complex.reCLM.hasSum (hs.sub hz).hasSum).div_const 2
  have heq :
      (fun p : RiemannXiDivisorZeroIndex =>
        ((1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p) -
          (1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)).re / 2) =
      (fun p : RiemannXiDivisorZeroIndex =>
        pairedResolventMean r
          ((riemannXiDivisorZeroValue p).re - 1 / 2)
          (t - (riemannXiDivisorZeroValue p).im)) := by
    funext p
    rw [show (1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p) -
        (1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p) =
        1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) -
        1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p) by ring]
    exact xiResolvent_real_difference r t (riemannXiDivisorZeroValue p)
  rw [<- heq]
  exact hh.summable

theorem xi_paired_resolvent_trace (r t : Real) (hr : 1 / 2 < r) :
    xiPairedLogTrace r t =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        pairedResolventMean r
          ((riemannXiDivisorZeroValue p).re - 1 / 2)
          (t - (riemannXiDivisorZeroValue p).im)) := by
  have hDiff := xi_logDeriv_sub_eq_tsum
    (xiResolventPoint r t) (xiResolventPoint (-r) t)
    (fun p => (xiResolventPoint_away r t hr p).1)
    (fun p => (xiResolventPoint_away r t hr p).2)
    (xi_point_genus_summable r t hr).1 (xi_point_genus_summable r t hr).2
  have hs := (xi_point_genus_summable r t hr).1
  have hz := (xi_point_genus_summable r t hr).2
  have hSummable :
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) -
        1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p)) := by
    convert hs.sub hz using 1
    funext p
    ring
  have hReal := congrArg (fun z : Complex => z.re / 2) hDiff
  have hRefl : logDeriv riemannXi (xiResolventPoint (-r) t) =
      -logDeriv riemannXi (xiResolventPoint r (-t)) := by
    rw [xiResolventPoint_reflection, xi_logDeriv_one_sub]
  rw [hRefl, sub_neg_eq_add, Complex.add_re] at hReal
  change xiPairedLogTrace r t = _ at hReal
  rw [show (tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) -
      1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p))).re / 2 =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / (xiResolventPoint r t - riemannXiDivisorZeroValue p) -
          1 / (xiResolventPoint (-r) t - riemannXiDivisorZeroValue p)).re / 2) by
    exact ((Complex.reCLM.hasSum hSummable.hasSum).div_const 2).tsum_eq.symm] at hReal
  rw [hReal]
  apply tsum_congr
  intro p
  exact xiResolvent_real_difference r t (riemannXiDivisorZeroValue p)

theorem xi_compensated_resolvent_summable (r R t : Real)
    (hr : 1 / 2 < r) (hR : r < R) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      pairedResolventDifference r R
        ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (t - (riemannXiDivisorZeroValue p).im)) := by
  exact (xi_paired_resolvent_summable r t hr).sub
    ((xi_paired_resolvent_summable R t (hr.trans hR)).mul_left (r / R))

theorem xi_compensated_resolvent_trace (r R t : Real)
    (hr : 1 / 2 < r) (hR : r < R) :
    xiPairedLogTrace r t - r / R * xiPairedLogTrace R t =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        pairedResolventDifference r R
          ((riemannXiDivisorZeroValue p).re - 1 / 2)
          (t - (riemannXiDivisorZeroValue p).im)) := by
  rw [xi_paired_resolvent_trace r t hr,
    xi_paired_resolvent_trace R t (hr.trans hR)]
  rw [<- tsum_mul_left]
  exact ((xi_paired_resolvent_summable r t hr).tsum_sub
    ((xi_paired_resolvent_summable R t (hr.trans hR)).mul_left (r / R))).symm

theorem xi_compensated_resolvent_finite_mass (r R t : Real)
    (hr : 1 / 2 < r) (hR : r < R)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      And (abs ((riemannXiDivisorZeroValue p).re - 1 / 2) < r)
        (2 * ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 <= r ^ 2))
    (S : Finset RiemannXiDivisorZeroIndex) :
    (Finset.sum S (fun p =>
      pairedResolventDifference r R
        ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (t - (riemannXiDivisorZeroValue p).im))) <=
      xiPairedLogTrace r t - r / R * xiPairedLogTrace R t := by
  rw [xi_compensated_resolvent_trace r R t hr hR]
  exact (xi_compensated_resolvent_summable r R t hr hR).sum_le_tsum S
    (fun p _ => pairedResolventDifference_nonneg r R _ _
      (hStrip p).1 hR (hStrip p).2)

end PrimeFactorOscillations
