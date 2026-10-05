/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Normalized linear products

A quadratic local bound gives uniform convergence on compact disks and
holomorphy of products with nonnegative square-summable parameters at most one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- The normalized linear factor loses only a quadratic amount in its
logarithm; no smallness assumption on the nonnegative real parameter. -/
theorem sub_log_one_add_bounds (a : Real) (ha : 0 <= a) :
    0 <= a - log (1 + a) /\ a - log (1 + a) <= a ^ 2 / 2 := by
  have hpos : 0 < 1 + a := by linarith
  have hupper := log_le_sub_one_of_pos hpos
  have hlower := le_log_one_add_of_nonneg ha
  have hden : Not (a + 2 = 0) := by linarith
  have hidentity : 2 * a / (a + 2) - (a - a ^ 2 / 2) =
      a ^ 3 / (2 * (a + 2)) := by
    field_simp
    ring
  have hnonneg : 0 <= a ^ 3 / (2 * (a + 2)) := by positivity
  rw [<- hidentity] at hnonneg
  constructor <;> linarith

end Real

namespace Complex

/-- Linear factor normalized to take value one at zero and at one. -/
noncomputable def normalizedLinearFactor (a : Real) (z : Complex) : Complex :=
  (1 + (a : Complex) * z) * exp (-(Real.log (1 + a) : Complex) * z)

/-- The deviation from one has a summable quadratic majorant on each disk. -/
theorem norm_normalizedLinearFactor_sub_one_le
    (a R : Real) (z : Complex) (ha : 0 <= a) (ha1 : a <= 1)
    (hR : 0 <= R) (hz : norm z <= R) :
    norm (normalizedLinearFactor a z - 1) <=
      ((R / 2 + R ^ 2 * Real.exp R) * Real.exp R) * a ^ 2 := by
  let b := Real.log (1 + a)
  let w : Complex := (b : Complex) * z
  have hb0 : 0 <= b := Real.log_nonneg (by linarith)
  have herr := Real.sub_log_one_add_bounds a ha
  have hba : b <= a := by dsimp [b]; linarith [herr.1]
  have herror : a - b <= a ^ 2 / 2 := herr.2
  have hab : 0 <= a - b := sub_nonneg.mpr hba
  have hw : norm w <= a * R := by
    calc
      norm w = b * norm z := by
        simp only [w, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      _ <= a * R := mul_le_mul hba hz (norm_nonneg z) ha
  have hwR : norm w <= R := hw.trans (mul_le_of_le_one_left hR ha1)
  have hexp : norm (exp (-w)) <= Real.exp R := by
    exact (norm_exp_le_exp_norm (-w)).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_neg] using hwR))
  have hrem : norm (exp w - 1 - w) <= norm w ^ 2 * Real.exp (norm w) := by
    simpa [Finset.sum_range_succ, Nat.factorial, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using norm_exp_sub_sum_le_norm_mul_exp w 2
  have hremBound : norm (exp w - 1 - w) <=
      a ^ 2 * R ^ 2 * Real.exp R := by
    calc
      norm (exp w - 1 - w) <= norm w ^ 2 * Real.exp (norm w) := hrem
      _ <= (a * R) ^ 2 * Real.exp R := by gcongr
      _ = a ^ 2 * R ^ 2 * Real.exp R := by ring
  have hlinear : norm (((a : Complex) - (b : Complex)) * z) <= a ^ 2 / 2 * R := by
    calc
      norm (((a : Complex) - (b : Complex)) * z) = (a - b) * norm z := by
        rw [<- ofReal_sub, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hab]
      _ <= a ^ 2 / 2 * R := mul_le_mul herror hz (norm_nonneg z) (by positivity)
  have he : exp w * exp (-w) = 1 := by
    rw [<- exp_add, add_neg_cancel, exp_zero]
  have hid : normalizedLinearFactor a z - 1 =
      (((a : Complex) - (b : Complex)) * z - (exp w - 1 - w)) * exp (-w) := by
    have hn : -(b : Complex) * z = -w := by dsimp [w]; ring
    change (1 + (a : Complex) * z) * exp (-(b : Complex) * z) - 1 = _
    rw [hn]
    calc
      (1 + (a : Complex) * z) * exp (-w) - 1 =
          (1 + (a : Complex) * z) * exp (-w) - exp w * exp (-w) := by rw [he]
      _ = (((a : Complex) - (b : Complex)) * z - (exp w - 1 - w)) * exp (-w) := by
        dsimp [w]
        ring
  rw [hid, norm_mul]
  have hsum := (norm_sub_le (((a : Complex) - (b : Complex)) * z)
    (exp w - 1 - w)).trans (add_le_add hlinear hremBound)
  calc
    norm (((a : Complex) - (b : Complex)) * z - (exp w - 1 - w)) * norm (exp (-w)) <=
        (a ^ 2 / 2 * R + a ^ 2 * R ^ 2 * Real.exp R) * Real.exp R :=
      mul_le_mul hsum hexp (norm_nonneg _) (by positivity)
    _ = ((R / 2 + R ^ 2 * Real.exp R) * Real.exp R) * a ^ 2 := by ring

@[simp] theorem normalizedLinearFactor_zero (a : Real) :
    normalizedLinearFactor a 0 = 1 := by
  simp [normalizedLinearFactor]

@[simp] theorem normalizedLinearFactor_one (a : Real) (ha : 0 <= a) :
    normalizedLinearFactor a 1 = 1 := by
  have hpos : 0 < 1 + a := by linarith
  have hne : Not (1 + (a : Complex) = 0) := by
    exact_mod_cast ne_of_gt hpos
  have he : exp (Real.log (1 + a) : Complex) = 1 + (a : Complex) := by
    rw [<- ofReal_exp, Real.exp_log hpos, ofReal_add, ofReal_one]
  simp only [normalizedLinearFactor, mul_one, exp_neg, he]
  field_simp

/-- Square-summable parameters make the normalized product converge uniformly
on every closed complex disk, including disks containing factor zeros. -/
theorem hasProdUniformlyOn_normalizedLinearFactor {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (R : Real) (hR : 0 <= R) :
    HasProdUniformlyOn (fun i z => normalizedLinearFactor (a i) z)
      (fun z => tprod (fun i => normalizedLinearFactor (a i) z))
      (Metric.closedBall (0 : Complex) R) := by
  let K := (R / 2 + R ^ 2 * Real.exp R) * Real.exp R
  have hbound : forall i, forall z,
      Membership.mem (Metric.closedBall (0 : Complex) R) z ->
        norm (normalizedLinearFactor (a i) z - 1) <= K * (a i) ^ 2 := by
    intro i z hz
    apply norm_normalizedLinearFactor_sub_one_le (a i) R z (ha i) (ha1 i) hR
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hcts : forall i, ContinuousOn (fun z => normalizedLinearFactor (a i) z - 1)
      (Metric.closedBall (0 : Complex) R) := by
    intro i
    apply Continuous.continuousOn
    unfold normalizedLinearFactor
    fun_prop
  have hp := Summable.hasProdUniformlyOn_one_add
    (f := fun i z => normalizedLinearFactor (a i) z - 1)
    (isCompact_closedBall (0 : Complex) R) (hs.mul_left K)
    (Filter.Eventually.of_forall hbound) hcts
  simpa only [add_sub_cancel] using hp

/-- The normalized infinite product is entire. Only cached uniform-product
and holomorphic-limit theorems are used. -/
theorem differentiable_tprod_normalizedLinearFactor {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) :
    Differentiable Complex (fun z => tprod (fun i => normalizedLinearFactor (a i) z)) := by
  intro z
  let R := norm z + 1
  have hR : 0 <= R := by dsimp [R]; positivity
  have hp := hasProdUniformlyOn_normalizedLinearFactor a ha ha1 hs R hR
  have hlim : TendstoLocallyUniformlyOn
      (fun s : Finset I => fun w => s.prod (fun i => normalizedLinearFactor (a i) w))
      (fun w => tprod (fun i => normalizedLinearFactor (a i) w))
      Filter.atTop (Metric.ball (0 : Complex) R) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall s : Finset I,
      Differentiable Complex (fun w => s.prod (fun i => normalizedLinearFactor (a i) w)) := by
    intro s
    unfold normalizedLinearFactor
    fun_prop
  have hd := hlim.differentiableOn
    (Filter.Eventually.of_forall (fun s => (hfin s).differentiableOn)) Metric.isOpen_ball
  have hz : Membership.mem (Metric.ball (0 : Complex) R) z := by
    simpa only [Metric.mem_ball, dist_zero_right, R] using lt_add_one (norm z)
  exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem normalizedLinearFactor_ofReal_eq (a t : Real)
    (ha : 0 <= a) (ht : 0 <= t) :
    Complex.normalizedLinearFactor a (t : Complex) =
      (Real.exp (Real.log (1 + a * t) - Real.log (1 + a) * t) : Complex) := by
  have hpos : 0 < 1 + a * t := by positivity
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hpos]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_neg, Complex.ofReal_exp, Complex.normalizedLinearFactor,
    neg_mul]


end Complex
