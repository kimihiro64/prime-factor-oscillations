/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# PeriodicCompanionGrowth

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
open MeasureTheory Filter Asymptotics

namespace PrimeFactorOscillations.PeriodicCompanion

def blockPrefix (f : Nat -> Complex) (N : Nat) : Complex :=
  (Finset.range N).sum f

theorem periodic_zero_block_prefix_bound
    (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hzero : blockPrefix f q = 0) (B : Real) (hB : 0 <= B)
    (hbound : forall n : Nat, norm (f n) <= B) (N : Nat) :
    norm (blockPrefix f N) <= (q : Real) * B := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < q
    . calc
        _ <= (Finset.range N).sum (fun n => norm (f n)) := norm_sum_le _ _
        _ <= (Finset.range N).sum (fun _ => B) :=
          Finset.sum_le_sum (fun n _ => hbound n)
        _ = (N : Real) * B := by simp
        _ <= (q : Real) * B :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hB
    . have hqN : q <= N := Nat.le_of_not_gt hN
      have hsub : N - q < N := Nat.sub_lt (hq.trans_le hqN) hq
      have hsplit : blockPrefix f N = blockPrefix f (N - q) := by
        have he : N = q + (N - q) := by omega
        unfold blockPrefix
        nth_rw 1 [he]
        rw [Finset.sum_range_add]
        change blockPrefix f q + _ = _
        rw [hzero, zero_add]
        apply Finset.sum_congr rfl
        intro n _
        simpa only [Nat.add_comm q n] using hf n
      rw [hsplit]
      exact ih (N - q) hsub

def mean (f : Nat -> Complex) (q : Nat) : Complex :=
  blockPrefix f q / (q : Complex)

def centered (f : Nat -> Complex) (q : Nat) (n : Nat) : Complex :=
  f n - mean f q

theorem centered_block_zero (f : Nat -> Complex) (q : Nat) (hq : Not (q = 0)) :
    blockPrefix (centered f q) q = 0 := by
  unfold blockPrefix centered
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold mean blockPrefix
  have hqc : Not ((q : Complex) = 0) := by exact_mod_cast hq
  field_simp
  ring

theorem centered_prefix_bound (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (N : Nat) :
    norm (blockPrefix (centered f q) N) <=
      (q : Real) * (1 + norm (mean f q)) := by
  apply periodic_zero_block_prefix_bound (centered f q) q hq
  . intro n
    simp only [centered, hf]
  . exact centered_block_zero f q (Nat.ne_of_gt hq)
  . positivity
  . intro n
    exact (norm_sub_le _ _).trans (add_le_add (hbound n) (le_refl _))

def floorError (f : Nat -> Complex) (q : Nat) (t : Real) : Complex :=
  blockPrefix f (Nat.floor t) - mean f q * (t : Complex)

theorem floorError_eq (f : Nat -> Complex) (q : Nat) (t : Real) :
    floorError f q t = blockPrefix (centered f q) (Nat.floor t) +
      mean f q * (((Nat.floor t : Nat) : Complex) - (t : Complex)) := by
  unfold floorError blockPrefix centered
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem floorError_bound (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (t : Real) (ht : 0 <= t) :
    norm (floorError f q t) <=
      (q : Real) * (1 + norm (mean f q)) + norm (mean f q) := by
  have hfl := Nat.floor_le ht
  have hlt := Nat.lt_floor_add_one t
  have habs : abs (((Nat.floor t : Nat) : Real) - t) <= 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hfl)]
    linarith
  have herr : norm (((Nat.floor t : Nat) : Complex) - (t : Complex)) <= 1 := by
    have he : ((Nat.floor t : Nat) : Complex) - (t : Complex) =
        ((((Nat.floor t : Nat) : Real) - t : Real) : Complex) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact habs
  rw [floorError_eq]
  calc
    _ <= norm (blockPrefix (centered f q) (Nat.floor t)) +
        norm (mean f q * (((Nat.floor t : Nat) : Complex) - (t : Complex))) :=
      norm_add_le _ _
    _ <= (q : Real) * (1 + norm (mean f q)) + norm (mean f q) * 1 := by
      rw [norm_mul]
      exact add_le_add (centered_prefix_bound f q hq hf hbound (Nat.floor t))
        (mul_le_mul_of_nonneg_left herr (norm_nonneg _))
    _ = _ := by ring

theorem floorError_measurable (f : Nat -> Complex) (q : Nat) :
    Measurable (floorError f q) := by
  exact ((measurable_of_countable (blockPrefix f)).comp Nat.measurable_floor).sub
    (measurable_const.mul Complex.continuous_ofReal.measurable)

def cutError (f : Nat -> Complex) (q : Nat) : Real -> Complex :=
  (Set.Ioi (1 : Real)).indicator (floorError f q)

theorem cutError_zero (f : Nat -> Complex) (q : Nat) (t : Real) (ht : t <= 1) :
    cutError f q t = 0 := by
  exact Set.indicator_of_notMem (not_lt.mpr ht) _

theorem cutError_measurable (f : Nat -> Complex) (q : Nat) :
    Measurable (cutError f q) :=
  (floorError_measurable f q).indicator measurableSet_Ioi

theorem cutError_bound (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (t : Real) :
    norm (cutError f q t) <=
      (q : Real) * (1 + norm (mean f q)) + norm (mean f q) := by
  by_cases ht : 1 < t
  . rw [cutError, Set.indicator_of_mem (s := Set.Ioi (1 : Real)) ht]
    exact floorError_bound f q hq hf hbound t (by linarith)
  . rw [cutError_zero f q t (le_of_not_gt ht), norm_zero]
    positivity

theorem cutError_locallyIntegrable (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) :
    LocallyIntegrable (cutError f q) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply IntegrableOn.of_bound hK.measure_lt_top
    ((cutError_measurable f q).aestronglyMeasurable.restrict)
    ((q : Real) * (1 + norm (mean f q)) + norm (mean f q))
  exact ae_of_all _ (cutError_bound f q hq hf hbound)

theorem cutError_top_bound (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) :
    IsBigO atTop (cutError f q) (fun t : Real => t ^ (-(0 : Real))) := by
  apply IsBigO.of_bound ((q : Real) * (1 + norm (mean f q)) + norm (mean f q))
  apply Filter.Eventually.of_forall
  intro t
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
    cutError_bound f q hq hf hbound t

theorem cutError_bottom_bound (f : Nat -> Complex) (q : Nat) (b : Real) :
    IsBigO (nhdsWithin (0 : Real) (Set.Ioi 0)) (cutError f q)
      (fun t : Real => t ^ (-b)) := by
  apply IsBigO.of_bound 0
  have he : forall t : Real, t < 1 -> norm (cutError f q t) <=
      0 * norm (t ^ (-b)) := by
    intro t ht
    rw [cutError_zero f q t ht.le, norm_zero, zero_mul]
  exact ((eventually_lt_nhds (show (0 : Real) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds).mono he

def errorMellin (f : Nat -> Complex) (q : Nat) (s : Complex) : Complex :=
  mellin (cutError f q) (-s)

theorem errorMellin_differentiableAt (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (s : Complex) (hs : 0 < s.re) :
    DifferentiableAt Complex (errorMellin f q) s := by
  have hd := mellin_differentiableAt_of_isBigO_rpow
    ((cutError_locallyIntegrable f q hq hf hbound).locallyIntegrableOn (Set.Ioi 0))
    (cutError_top_bound f q hq hf hbound)
    (show (-s).re < (0 : Real) by simpa using neg_lt_zero.mpr hs)
    (cutError_bottom_bound f q ((-s).re - 1)) (by linarith)
  exact hd.comp s (differentiableAt_id.neg)

theorem errorMellin_eq_integral (f : Nat -> Complex) (q : Nat) (s : Complex) :
    errorMellin f q s =
      integral (volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => (t : Complex) ^ (-s - 1) * floorError f q t) := by
  have he : (fun t : Real => (t : Complex) ^ (-s - 1) * cutError f q t) =
      (Set.Ioi (1 : Real)).indicator
        (fun t : Real => (t : Complex) ^ (-s - 1) * floorError f q t) := by
    funext t
    by_cases ht : Membership.mem (Set.Ioi (1 : Real)) t
    . rw [cutError, Set.indicator_of_mem (s := Set.Ioi (1 : Real)) ht,
        Set.indicator_of_mem (s := Set.Ioi (1 : Real)) ht]
    . rw [cutError, Set.indicator_of_notMem (s := Set.Ioi (1 : Real)) ht,
        Set.indicator_of_notMem (s := Set.Ioi (1 : Real)) ht, mul_zero]
  unfold errorMellin mellin
  simp only [smul_eq_mul]
  rw [he, setIntegral_indicator measurableSet_Ioi]
  have hset : Inter.inter (Set.Ioi (0 : Real)) (Set.Ioi (1 : Real)) = Set.Ioi (1 : Real) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    . exact And.right
    . intro ht
      exact And.intro (lt_trans (show (0 : Real) < 1 by norm_num) ht) ht
  rw [hset]

theorem errorMellin_norm_bound (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (s : Complex) (hs : 0 < s.re) :
    norm (errorMellin f q s) <=
      ((q : Real) * (1 + norm (mean f q)) + norm (mean f q)) / s.re := by
  let B : Real := (q : Real) * (1 + norm (mean f q)) + norm (mean f q)
  rw [errorMellin_eq_integral]
  calc
    _ <= integral (volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => B * t ^ (-s.re - 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
          (by norm_num : (0 : Real) < 1)).const_mul B)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans zero_lt_one ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      calc
        _ <= t ^ (-s.re - 1) * B :=
          mul_le_mul_of_nonneg_left (floorError_bound f q hq hf hbound t htpos.le)
            (Real.rpow_nonneg htpos.le _)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
        (by norm_num : (0 : Real) < 1), Real.one_rpow,
        show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]
      dsimp [B]
      ring

end PrimeFactorOscillations.PeriodicCompanion
