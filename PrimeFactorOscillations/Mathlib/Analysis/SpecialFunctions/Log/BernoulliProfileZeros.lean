/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.LinearCombination
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.NormalizedLinearProduct

/-!
# Zeros of canonical Bernoulli profiles

Square-summable nonnegative parameters at most one define an entire compensated
Bernoulli product. Its zeros come exactly from its linear factors. Reindexing
preserves the product. These are analytic inputs to prime-labelled inverse
theorems; multiplicity recovery is a separate step.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- The compensated Bernoulli factor centred at one. -/
def canonicalBernoulliFactor (a : Real) (z : Complex) : Complex :=
  (1 + (a : Complex) * (z - 1)) * exp (-(a : Complex) * (z - 1))

/-- The canonical product of compensated Bernoulli factors. -/
def canonicalBernoulliProfile {I : Type*} (a : I -> Real) (z : Complex) : Complex :=
  tprod (fun i => canonicalBernoulliFactor (a i) z)

/-- A quadratic bound uniform on a disk centred at one. -/
theorem norm_canonicalBernoulliFactor_sub_one_le
    (a R : Real) (z : Complex) (ha : 0 <= a) (ha1 : a <= 1)
    (hR : 0 <= R) (hz : norm (z - 1) <= R) :
    norm (canonicalBernoulliFactor a z - 1) <=
      (R ^ 2 * Real.exp R * Real.exp R) * a ^ 2 := by
  let w : Complex := (a : Complex) * (z - 1)
  have hw : norm w <= a * R := by
    simpa only [w, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left hz ha
  have hwR : norm w <= R := hw.trans (mul_le_of_le_one_left hR ha1)
  have hexp : norm (exp (-w)) <= Real.exp R :=
    (norm_exp_le_exp_norm (-w)).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_neg] using hwR))
  have hrem : norm (exp w - 1 - w) <= norm w ^ 2 * Real.exp (norm w) := by
    simpa [Finset.sum_range_succ, Nat.factorial, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using norm_exp_sub_sum_le_norm_mul_exp w 2
  have hremBound : norm (exp w - 1 - w) <= a ^ 2 * R ^ 2 * Real.exp R := by
    calc
      norm (exp w - 1 - w) <= norm w ^ 2 * Real.exp (norm w) := hrem
      _ <= (a * R) ^ 2 * Real.exp R := by gcongr
      _ = a ^ 2 * R ^ 2 * Real.exp R := by ring
  have he : exp w * exp (-w) = 1 := by
    rw [<- exp_add, add_neg_cancel, exp_zero]
  have hid : canonicalBernoulliFactor a z - 1 =
      -(exp w - 1 - w) * exp (-w) := by
    have hn : -(a : Complex) * (z - 1) = -w := by dsimp [w]; ring
    change (1 + w) * exp (-(a : Complex) * (z - 1)) - 1 = _
    rw [hn]
    calc
      (1 + w) * exp (-w) - 1 = (1 + w) * exp (-w) - exp w * exp (-w) := by rw [he]
      _ = _ := by ring
  rw [hid, norm_mul, norm_neg]
  calc
    norm (exp w - 1 - w) * norm (exp (-w)) <=
        (a ^ 2 * R ^ 2 * Real.exp R) * Real.exp R :=
      mul_le_mul hremBound hexp (norm_nonneg _) (by positivity)
    _ = (R ^ 2 * Real.exp R * Real.exp R) * a ^ 2 := by ring

/-- At each point the factor deviations have summable norms. -/
theorem summable_norm_canonicalBernoulliFactor_sub_one {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (z : Complex) :
    Summable (fun i => norm (canonicalBernoulliFactor (a i) z - 1)) := by
  let R : Real := norm (z - 1)
  exact (hs.mul_left (R ^ 2 * Real.exp R * Real.exp R)).of_nonneg_of_le
    (fun i => norm_nonneg _) (fun i =>
      norm_canonicalBernoulliFactor_sub_one_le (a i) R z
        (ha i) (ha1 i) (norm_nonneg _) le_rfl)

/-- Uniform convergence holds on disks that contain factor zeros as well. -/
theorem hasProdUniformlyOn_canonicalBernoulliFactor {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (R : Real) (hR : 0 <= R) :
    HasProdUniformlyOn (fun i z => canonicalBernoulliFactor (a i) z)
      (canonicalBernoulliProfile a) (Metric.closedBall (1 : Complex) R) := by
  let K := R ^ 2 * Real.exp R * Real.exp R
  have hbound : forall i, forall z,
      Membership.mem (Metric.closedBall (1 : Complex) R) z ->
        norm (canonicalBernoulliFactor (a i) z - 1) <= K * (a i) ^ 2 := by
    intro i z hz
    apply norm_canonicalBernoulliFactor_sub_one_le (a i) R z (ha i) (ha1 i) hR
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hcts : forall i, ContinuousOn (fun z => canonicalBernoulliFactor (a i) z - 1)
      (Metric.closedBall (1 : Complex) R) := by
    intro i
    apply Continuous.continuousOn
    unfold canonicalBernoulliFactor
    fun_prop
  have hp := Summable.hasProdUniformlyOn_one_add
    (f := fun i z => canonicalBernoulliFactor (a i) z - 1)
    (isCompact_closedBall (1 : Complex) R) (hs.mul_left K)
    (Filter.Eventually.of_forall hbound) hcts
  convert hp using 1 <;> simp only [add_sub_cancel]
  rfl

/-- The canonical Bernoulli profile is entire. -/
theorem differentiable_canonicalBernoulliProfile {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) :
    Differentiable Complex (canonicalBernoulliProfile a) := by
  intro z
  let R := norm (z - 1) + 1
  have hR : 0 <= R := by dsimp [R]; positivity
  have hp := hasProdUniformlyOn_canonicalBernoulliFactor a ha ha1 hs R hR
  have hlim : TendstoLocallyUniformlyOn
      (fun s : Finset I => fun w => s.prod (fun i => canonicalBernoulliFactor (a i) w))
      (canonicalBernoulliProfile a)
      Filter.atTop (Metric.ball (1 : Complex) R) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall s : Finset I,
      Differentiable Complex (fun w => s.prod (fun i => canonicalBernoulliFactor (a i) w)) := by
    intro s
    unfold canonicalBernoulliFactor
    fun_prop
  have hd := hlim.differentiableOn
    (Filter.Eventually.of_forall (fun s => (hfin s).differentiableOn)) Metric.isOpen_ball
  have hz : Membership.mem (Metric.ball (1 : Complex) R) z := by
    simpa only [Metric.mem_ball, dist_eq_norm, R] using lt_add_one (norm (z - 1))
  exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)

/-- Each nonzero parameter contributes its prescribed zero. -/
theorem canonicalBernoulliFactor_eq_zero_iff (a : Real) (z : Complex) :
    canonicalBernoulliFactor a z = 0 <->
      Not (a = 0) /\ z = 1 - 1 / (a : Complex) := by
  simp only [canonicalBernoulliFactor, mul_eq_zero, exp_ne_zero, or_false]
  constructor
  . intro h
    have ha : Not (a = 0) := by
      intro ha
      simp [ha] at h
    have haC : Not ((a : Complex) = 0) := by exact_mod_cast ha
    refine And.intro ha ?_
    field_simp
    linear_combination h
  . intro h
    have haC : Not ((a : Complex) = 0) := by exact_mod_cast h.1
    rw [h.2]
    field_simp
    ring

/-- The infinite product has no additional zeros. -/
theorem canonicalBernoulliProfile_eq_zero_iff {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (z : Complex) :
    canonicalBernoulliProfile a z = 0 <->
      exists i, Not (a i = 0) /\ z = 1 - 1 / (a i : Complex) := by
  have hraw : canonicalBernoulliProfile a z = 0 <->
      exists i, canonicalBernoulliFactor (a i) z = 0 := by
    constructor
    . intro hz
      by_contra hn
      have hne : forall i, Not (1 + (canonicalBernoulliFactor (a i) z - 1) = 0) := by
        intro i hi
        simp only [add_sub_cancel] at hi
        exact hn (Exists.intro i hi)
      have hp := tprod_one_add_ne_zero_of_summable hne
        (summable_norm_canonicalBernoulliFactor_sub_one a ha ha1 hs z)
      simp only [add_sub_cancel] at hp
      exact hp hz
    . intro hi
      exact tprod_of_exists_eq_zero hi
  simpa only [canonicalBernoulliFactor_eq_zero_iff] using hraw

/-- Every bijective relabelling preserves the profile. -/
theorem canonicalBernoulliProfile_comp_equiv {I J : Type*}
    (a : I -> Real) (e : Equiv J I) (z : Complex) :
    canonicalBernoulliProfile (fun j => a (e j)) z = canonicalBernoulliProfile a z := by
  exact e.tprod_eq (fun i => canonicalBernoulliFactor (a i) z)

end Complex
