/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticCompensatedSubpower

/-!
# QuadraticRetainedBeta

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticRetainedBeta

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticMainTermCancellation QuadraticPrincipalBoundary
open QuadraticCompensatedEstimate QuadraticCompensatedSubpower

theorem beta_mean_bound (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N1 N2 : Nat)
        (S T : Finset Nat) (a b : Nat -> Complex),
      0 < K ->
      (forall p, Membership.mem G p -> Nat.Prime p /\ Odd p) ->
      (forall v, Membership.mem V v ->
        0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      norm (beta G V K (weightedForm S T a b)) <=
        C * (subsetProduct G : Real) ^ eps *
          ((max N1 N2 : Nat) : Real) ^ eps * meanCap K N1 N2 S T a b := by
  choose C hC hc using weighted_tag_mean eps heps
  choose A hA ha using tag_count_subpower eps heps
  refine Exists.intro (A * C) (And.intro (mul_pos hA hC) ?_)
  intro G V K N1 N2 S T a b hK hG hV hS hT
  let R := V.filter (fun v => v <= K)
  let L := C * ((max N1 N2 : Nat) : Real) ^ eps * meanCap K N1 N2 S T a b
  have hL : 0 <= L := by dsimp only [L, meanCap]; positivity
  have htag (U : Finset Nat) (hU : Membership.mem G.powerset U) :
      norm (V.sum (fun v => if v <= K then
        (-1 : Complex) ^ U.card *
          weightedForm S T a b ((subsetProduct U) ^ 2 * v) else 0)) <= L := by
    have hrows : forall v, Membership.mem R v ->
        Membership.mem (columns K) (1 * v) := by
      intro v hv
      have hvF := Finset.mem_filter.mp hv
      have hx := lifted_columns G (EmptyCollection.emptyCollection : Finset Nat)
        (Finset.empty_subset G) hG K v (hV v hvF.1)
        (by simpa only [subsetProduct, Finset.prod_empty, one_mul] using hvF.2)
      simpa only [subsetProduct, Finset.prod_empty, one_mul] using hx
    have hfreq : forall v, Membership.mem R v ->
        1 <= (subsetProduct U) ^ 2 * (1 * v) := by
      intro v hv
      have hvpos := (hV v (Finset.mem_filter.mp hv).1).1
      have hu := subsetProduct_one_le G U (fun p hp => (hG p hp).1.one_le) hU
      have hu2 : 1 <= (subsetProduct U) ^ 2 := by nlinarith
      simpa only [one_mul] using Nat.mul_le_mul hu2 hvpos
    have hb := hc K N1 N2 1 (subsetProduct U) 1
      (by decide) (by decide) R S T a b hrows hfreq hS hT
    have heq :
        V.sum (fun v => if v <= K then
          (-1 : Complex) ^ U.card *
            weightedForm S T a b ((subsetProduct U) ^ 2 * v) else 0) =
        (-1 : Complex) ^ U.card *
          R.sum (fun v => weightedForm S T a b ((subsetProduct U) ^ 2 * v)) := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [heq, norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    apply (norm_sum_le _ _).trans
    simpa only [Nat.cast_one, Real.sqrt_one, one_div_one, one_mul] using hb
  have hcard : (G.powerset.card : Real) <= A * (subsetProduct G : Real) ^ eps := by
    have ht := ha G (fun p hp => (hG p hp).1)
    nlinarith [sq_nonneg (G.powerset.card : Real)]
  calc
    _ <= G.powerset.sum (fun U => norm (V.sum (fun v => if v <= K then
        (-1 : Complex) ^ U.card *
          weightedForm S T a b ((subsetProduct U) ^ 2 * v) else 0))) := by
      rw [beta_reordered]
      exact norm_sum_le _ _
    _ <= G.powerset.sum (fun _ => L) := Finset.sum_le_sum htag
    _ = (G.powerset.card : Real) * L := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= (A * (subsetProduct G : Real) ^ eps) * L :=
      mul_le_mul_of_nonneg_right hcard hL
    _ = _ := by dsimp only [L]; ring

theorem retained_compensation_bound (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N1 N2 : Nat)
        (S T : Finset Nat) (a b : Nat -> Complex) (c : Complex),
      0 < K ->
      (forall p, Membership.mem G p -> Nat.Prime p /\ Odd p) ->
      (forall v, Membership.mem V v ->
        0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      norm (alpha G V K (weightedForm S T a b) -
        c * beta G V K (weightedForm S T a b)) <=
        C * (subsetProduct G : Real) ^ eps *
          ((max N1 N2 : Nat) : Real) ^ eps *
          ((1 / Real.sqrt (K : Real)) *
            meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b +
            norm (1 - c) * meanCap K N1 N2 S T a b) := by
  choose A hA ha using compensated_main_subpower eps heps
  choose B hB hb using beta_mean_bound eps heps
  refine Exists.intro (A + B) (And.intro (add_pos hA hB) ?_)
  intro G V K N1 N2 S T a b c hK hG hV hS hT
  let F := weightedForm S T a b
  let Z := (subsetProduct G : Real) ^ eps *
    ((max N1 N2 : Nat) : Real) ^ eps
  let X := (1 / Real.sqrt (K : Real)) *
    meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b
  let Y := norm (1 - c) * meanCap K N1 N2 S T a b
  have hZ : 0 <= Z := by dsimp only [Z]; positivity
  have hX : 0 <= X := by dsimp only [X, meanCap]; positivity
  have hY : 0 <= Y := by dsimp only [Y, meanCap]; positivity
  have hda : norm (alpha G V K F - beta G V K F) <= A * Z * X := by
    calc
      _ <= _ := ha G V K N1 N2 S T a b hK hG hV hS hT
      _ = _ := by dsimp only [Z, X]; ring
  have hdb : norm (1 - c) * norm (beta G V K F) <= B * Z * Y := by
    calc
      _ <= norm (1 - c) *
          (B * (subsetProduct G : Real) ^ eps *
            ((max N1 N2 : Nat) : Real) ^ eps * meanCap K N1 N2 S T a b) :=
        mul_le_mul_of_nonneg_left
          (hb G V K N1 N2 S T a b hK hG hV hS hT) (norm_nonneg _)
      _ = _ := by dsimp only [Z, Y]; ring
  have hid : alpha G V K F - c * beta G V K F =
      (alpha G V K F - beta G V K F) + (1 - c) * beta G V K F := by ring
  calc
    _ <= norm (alpha G V K F - beta G V K F) +
        norm (1 - c) * norm (beta G V K F) := by
      rw [hid]
      exact (norm_add_le _ _).trans (by rw [norm_mul])
    _ <= A * Z * X + B * Z * Y := add_le_add hda hdb
    _ <= (A + B) * Z * (X + Y) := by
      nlinarith [mul_nonneg (mul_nonneg hA.le hZ) hY,
        mul_nonneg (mul_nonneg hB.le hZ) hX]
    _ = _ := by dsimp only [Z, X, Y]; ring

end PrimeFactorOscillations.QuadraticRetainedBeta

