/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.LPFMajorLogDisc

/-!
# Constructing the normalized logarithm for the major-arc disk

Every nonvanishing analytic function on a ball has a normalized logarithm,
constructed from a primitive of its logarithmic derivative. Its relative
growth bound then supplies the explicit 3328 B derivative estimate.
The growth bounds for the actual L-functions are separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_normalized_log_on_ball (f : Complex -> Complex)
    (c : Complex) (r : Real) (hr : 0 < r)
    (hf : AnalyticOnNhd Complex f (Metric.ball c r))
    (hn : forall w, Membership.mem (Metric.ball c r) w -> Not (f w = 0)) :
    Exists fun g : Complex -> Complex =>
      g c = 0 /\
      (forall w, Membership.mem (Metric.ball c r) w ->
        HasDerivAt g (deriv f w / f w) w) /\
      (forall w, Membership.mem (Metric.ball c r) w ->
        Complex.exp (g w) * f c = f w) := by
  have hd : DifferentiableOn Complex
      (fun w => deriv f w / f w) (Metric.ball c r) :=
    hf.deriv.differentiableOn.div hf.differentiableOn hn
  let hex := hd.isExactOn_ball.with_val_at c (0 : Complex)
  let g := Classical.choose hex
  have hg := Classical.choose_spec hex
  have hgc : g c = 0 := hg.1
  have hgd := hg.2
  let u : Complex -> Complex := fun w => Complex.exp (-g w) * f w
  have hu : forall w, Membership.mem (Metric.ball c r) w -> HasDerivAt u 0 w := by
    intro w hw
    have hwf := (hf w hw).differentiableAt.hasDerivAt
    have hwu := ((hgd w hw).neg.cexp).mul hwf
    convert hwu using 1
    dsimp
    field_simp [hn w hw]
    <;> ring
  have hud : DifferentiableOn Complex u (Metric.ball c r) := by
    intro w hw
    exact (hu w hw).differentiableAt.differentiableWithinAt
  have hu0 : Set.EqOn (deriv u) (0 : Complex -> Complex)
      (Metric.ball c r) := by
    intro w hw
    exact (hu w hw).deriv
  have hc : Membership.mem (Metric.ball c r) c := by
    simpa using hr
  refine Exists.intro g (And.intro hgc (And.intro hgd ?_))
  intro w hw
  have hi : Complex.exp (-g w) * f w = f c := by
    have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c r).isPreconnected hud hu0 hw hc
    simpa [u, hgc] using he
  calc
    Complex.exp (g w) * f c =
        Complex.exp (g w) * (Complex.exp (-g w) * f w) := by rw [hi]
    _ = (Complex.exp (g w) * Complex.exp (-g w)) * f w := by ring
    _ = f w := by rw [<- Complex.exp_add]; simp

theorem lpf_log_deriv_disc_growth_bound
    (f : Complex -> Complex) (c z : Complex) (B : Real) (hB : 0 < B)
    (hf : AnalyticOnNhd Complex f (Metric.ball c (9 / 8)))
    (hn : forall w, Membership.mem (Metric.ball c (9 / 8)) w -> Not (f w = 0))
    (hGrowth : forall w, Membership.mem (Metric.ball c (9 / 8)) w ->
      norm (f w) <= Real.exp B * norm (f c))
    (hz : dist z c <= 17 / 16) :
    norm (deriv f z / f z) <= 3328 * B := by
  let hex := lpf_normalized_log_on_ball f c (9 / 8) (by norm_num) hf hn
  let g := Classical.choose hex
  have hg := Classical.choose_spec hex
  have hc : Membership.mem (Metric.ball c (9 / 8)) c := by simp
  have hfc : 0 < norm (f c) := norm_pos_iff.mpr (hn c hc)
  have hRe : forall w, Membership.mem (Metric.ball c (9 / 8)) w -> (g w).re <= B := by
    intro w hw
    have hi := congrArg norm (hg.2.2 w hw)
    rw [norm_mul, Complex.norm_exp] at hi
    apply Real.exp_le_exp.mp
    apply (mul_le_mul_iff_of_pos_right hfc).mp
    calc
      Real.exp (g w).re * norm (f c) = norm (f w) := hi
      _ <= Real.exp B * norm (f c) := hGrowth w hw
  have hgd : DifferentiableOn Complex g (Metric.ball c (9 / 8)) := by
    intro w hw
    exact (hg.2.1 w hw).differentiableAt.differentiableWithinAt
  have hbound := lpf_log_disc_deriv_bound g c z B hB hgd hg.1 hRe hz
  have hzb : Membership.mem (Metric.ball c (9 / 8)) z := by
    change dist z c < 9 / 8
    linarith
  rwa [(hg.2.1 z hzb).deriv] at hbound

end PrimeFactorOscillations.QRH
