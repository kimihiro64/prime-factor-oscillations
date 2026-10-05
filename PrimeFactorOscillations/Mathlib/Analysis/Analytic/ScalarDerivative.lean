/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Derivatives of real scalar power series

The existing multilinear derivative-series API gives the first two scalar
derivatives and shows that scalar differentiation preserves the radius.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FormalMultilinearSeries

/-- Scalar power-series differentiation, derived from the existing
multilinear derivative-series theorem and evaluation of the summable series. -/
theorem hasDerivAt_scalarSeries (c : Nat -> Real) (x : Real)
    (hx : (nnnorm x : ENNReal) < (ofScalars Real c).radius) :
    HasDerivAt (fun y : Real => tsum (fun j : Nat => c j * y ^ j))
      (tsum (fun j : Nat => ((j : Real) + 1) * c (j + 1) * x ^ j)) x := by
  let p := ofScalars Real c
  have hdx : HasDerivAt p.sum ((p.derivSeries.sum x) 1) x :=
    (p.hasFDerivAt_sum hx).hasDerivAt
  have hsum : Summable (fun j : Nat => p.derivSeries j (fun _ => x)) :=
    (p.derivSeries.summable_norm_apply
      (by simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using
        hx.trans_le p.radius_le_radius_derivSeries)).of_norm
  have hvalue : (p.derivSeries.sum x) 1 =
      tsum (fun j : Nat => ((j : Real) + 1) * c (j + 1) * x ^ j) := by
    change (tsum (fun j : Nat => p.derivSeries j (fun _ => x))) 1 = _
    change (ContinuousLinearMap.apply Real Real (1 : Real))
      (tsum (fun j : Nat => p.derivSeries j (fun _ => x))) = _
    rw [(ContinuousLinearMap.apply Real Real (1 : Real)).map_tsum hsum]
    apply tsum_congr
    intro j
    simp only [ContinuousLinearMap.apply_apply]
    rw [apply_eq_pow_smul_coeff]
    simp only [_root_.smul_apply, derivSeries_coeff_one, p,
      coeff_ofScalars, nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hfunction : p.sum = fun y : Real => tsum (fun j : Nat => c j * y ^ j) := by
    funext y
    change ofScalarsSum c y = _
    simpa only [smul_eq_mul] using ofScalars_sum_eq c y
  rw [hfunction, hvalue] at hdx
  exact hdx

/-- Differentiation of a scalar series cannot reduce its convergence radius. -/
theorem radius_le_scalarDerivative_radius (c : Nat -> Real) :
    (ofScalars Real c).radius <=
      (ofScalars Real (fun j : Nat => ((j : Real) + 1) * c (j + 1))).radius := by
  let p := ofScalars Real c
  let ev := ContinuousLinearMap.apply Real Real (1 : Real)
  have hq : ev.compFormalMultilinearSeries p.derivSeries =
      ofScalars Real (fun j : Nat => ((j : Real) + 1) * c (j + 1)) := by
    apply funext
    intro j
    apply ContinuousMultilinearMap.ext
    intro v
    change (p.derivSeries j v) 1 =
      (ofScalars Real (fun j : Nat => ((j : Real) + 1) * c (j + 1)) j) v
    rw [apply_eq_prod_smul_coeff, apply_eq_prod_smul_coeff]
    simp only [_root_.smul_apply, derivSeries_coeff_one, p, coeff_ofScalars,
      nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hle := p.radius_le_radius_derivSeries.trans
    (p.derivSeries.radius_le_radius_continuousLinearMap_comp ev)
  rw [hq] at hle
  exact hle

/-- The second derivative is the twice-shifted coefficient series. -/
theorem hasDerivAt_scalarSeries_deriv (c : Nat -> Real) (x : Real)
    (hx : (nnnorm x : ENNReal) < (ofScalars Real c).radius) :
    HasDerivAt (deriv (fun y : Real => tsum (fun j : Nat => c j * y ^ j)))
      (tsum (fun j : Nat =>
        ((j : Real) + 1) * ((j : Real) + 2) * c (j + 2) * x ^ j)) x := by
  let c' := fun j : Nat => ((j : Real) + 1) * c (j + 1)
  have hd := hasDerivAt_scalarSeries c' x
    (hx.trans_le (radius_le_scalarDerivative_radius c))
  have hball : Membership.mem
      (Metric.eball (0 : Real) (ofScalars Real c).radius) x := by
    simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hx
  have heq : Filter.EventuallyEq (nhds x)
      (deriv (fun y : Real => tsum (fun j : Nat => c j * y ^ j)))
      (fun y : Real => tsum (fun j : Nat => c' j * y ^ j)) := by
    filter_upwards [Metric.isOpen_eball.mem_nhds hball] with y hy
    have hy' : (nnnorm y : ENNReal) < (ofScalars Real c).radius := by
      simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hy
    exact (hasDerivAt_scalarSeries c y hy').deriv
  have hfinal := hd.congr_of_eventuallyEq heq
  convert hfinal using 1
  apply tsum_congr
  intro j
  simp only [c', Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  ring

/-- The full quadratic factorial moment is exactly the scaled second
derivative. The vanished zeroth and first terms are included explicitly. -/
theorem tsum_factorial_secondMoment_eq (c : Nat -> Real) (x : Real)
    (hx : (nnnorm x : ENNReal) < (ofScalars Real c).radius) :
    tsum (fun j : Nat => c j * x ^ j * ((j : Real) * (j - 1))) =
      x ^ 2 * deriv (deriv (fun y : Real =>
        tsum (fun j : Nat => c j * y ^ j))) x := by
  let c1 := fun j : Nat => ((j : Real) + 1) * c (j + 1)
  let c2 := fun j : Nat => ((j : Real) + 1) * c1 (j + 1)
  have hx2 : (nnnorm x : ENNReal) < (ofScalars Real c2).radius :=
    (hx.trans_le (radius_le_scalarDerivative_radius c)).trans_le
      (radius_le_scalarDerivative_radius c1)
  have hraw : Summable (fun j : Nat => ofScalars Real c2 j (fun _ => x)) :=
    ((ofScalars Real c2).summable_norm_apply
      (by simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
        using hx2)).of_norm
  have hs : Summable (fun j : Nat =>
      ((j : Real) + 1) * ((j : Real) + 2) * c (j + 2) * x ^ j) := by
    convert hraw using 1
    funext j
    simp only [ofScalars_apply_eq, smul_eq_mul, c2, c1,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc]
    ring
  let w := fun j : Nat => c j * x ^ j * ((j : Real) * (j - 1))
  have hderiv := hasDerivAt_scalarSeries_deriv c x hx
  have htail : HasSum (fun j : Nat => w (j + 2))
      (x ^ 2 * deriv (deriv (fun y : Real =>
        tsum (fun j : Nat => c j * y ^ j))) x) := by
    rw [hderiv.deriv]
    convert hs.hasSum.mul_left (x ^ 2) using 1
    funext j
    simp only [w, Nat.cast_add, Nat.cast_ofNat, pow_add]
    ring
  have hall := htail.sum_range_add
  have hhead : (Finset.range 2).sum w = 0 := by
    norm_num [w, Finset.sum_range_succ]
  rw [hhead, zero_add] at hall
  exact hall.tsum_eq

end FormalMultilinearSeries
