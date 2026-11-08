/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Two-scale inverse limits at a zero with a local factorization -/

set_option autoImplicit false
set_option Elab.async false

namespace Complex

theorem tendsto_pow_mul_inverse_difference_of_factor
    (f g : Complex -> Complex) (rho c : Complex) (m : Nat)
    (hc : Not (c = 0)) (hg : ContinuousAt g rho) (hg0 : Not (g rho = 0))
    (hfg : Filter.Eventually
      (fun s => f s = (s - rho) ^ m * g s) (nhds rho)) :
    Filter.Tendsto
      (fun z : Complex => z ^ m * (1 / f (rho + z) - 1 / f (rho + c * z)))
      (nhdsWithin 0 (Set.compl {0}))
      (nhds ((1 - 1 / c ^ m) / g rho)) := by
  let l := nhdsWithin (0 : Complex) (Set.compl {0})
  have hz : Filter.Tendsto (fun z : Complex => z) l (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hOne : Filter.Tendsto (fun z : Complex => rho + z) l (nhds rho) := by
    simpa only [add_zero] using tendsto_const_nhds.add hz
  have hScale : Filter.Tendsto (fun z : Complex => rho + c * z) l (nhds rho) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
  have hInvOne : Filter.Tendsto
      (fun z : Complex => 1 / g (rho + z)) l (nhds (1 / g rho)) :=
    tendsto_const_nhds.div (hg.tendsto.comp hOne) hg0
  have hDen : Not (c ^ m * g rho = 0) :=
    mul_ne_zero (pow_ne_zero m hc) hg0
  have hInvScale : Filter.Tendsto
      (fun z : Complex => 1 / (c ^ m * g (rho + c * z)))
      l (nhds (1 / (c ^ m * g rho))) :=
    tendsto_const_nhds.div
      (tendsto_const_nhds.mul (hg.tendsto.comp hScale)) hDen
  have hLimit : Filter.Tendsto
      (fun z : Complex => 1 / g (rho + z) - 1 / (c ^ m * g (rho + c * z)))
      l (nhds (1 / g rho - 1 / (c ^ m * g rho))) :=
    hInvOne.sub hInvScale
  have hZero : Filter.Eventually (fun z : Complex => Not (z = 0)) l := by
    have hMem : Filter.Eventually
        (fun z : Complex => Membership.mem (Set.compl {0}) z) l :=
      self_mem_nhdsWithin
    apply hMem.mono
    intro z hz he
    apply hz
    rw [he]
    exact Set.mem_singleton 0
  have hNear := (hOne.eventually hfg).and ((hScale.eventually hfg).and
    ((hOne.eventually (hg.eventually_ne hg0)).and
      ((hScale.eventually (hg.eventually_ne hg0)).and hZero)))
  have hEq : Filter.EventuallyEq l
      (fun z : Complex => z ^ m * (1 / f (rho + z) - 1 / f (rho + c * z)))
      (fun z : Complex => 1 / g (rho + z) - 1 / (c ^ m * g (rho + c * z))) := by
    apply hNear.mono
    intro z h
    change z ^ m * (1 / f (rho + z) - 1 / f (rho + c * z)) =
      1 / g (rho + z) - 1 / (c ^ m * g (rho + c * z))
    rw [h.1, h.2.1]
    have hSubOne : rho + z - rho = z := by ring
    have hSubScale : rho + c * z - rho = c * z := by ring
    rw [hSubOne, hSubScale, mul_pow]
    field_simp [pow_ne_zero m h.2.2.2.2, pow_ne_zero m hc, h.2.2.1, h.2.2.2.1]
  have hConst : 1 / g rho - 1 / (c ^ m * g rho) =
      (1 - 1 / c ^ m) / g rho := by
    field_simp [pow_ne_zero m hc, hg0]
  rw [hConst] at hLimit
  exact (Filter.tendsto_congr' hEq).mpr hLimit

end Complex
