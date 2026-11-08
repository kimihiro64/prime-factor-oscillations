/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Two-scale inverse and three-scale quotient limits at a local zero -/

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

/-- The complete three-scale quotient retains the zero order and cancels its nonzero factor. -/
theorem tendsto_three_scale_ratio_of_factor
    (f g : Complex -> Complex) (rho : Complex) (m : Nat)
    (hg : ContinuousAt g rho) (hg0 : Not (g rho = 0))
    (hfg : Filter.Eventually
      (fun s => f s = (s - rho) ^ m * g s) (nhds rho)) :
    Filter.Tendsto
      (fun z : Complex =>
        f (rho + z) * f (rho + 3 * z) ^ 3 / f (rho + 2 * z) ^ 4)
      (nhdsWithin 0 (Set.compl {0}))
      (nhds ((27 / 16 : Complex) ^ m)) := by
  let l := nhdsWithin (0 : Complex) (Set.compl {0})
  let C : Complex := ((3 : Complex) ^ m) ^ 3 / ((2 : Complex) ^ m) ^ 4
  have hz : Filter.Tendsto (fun z : Complex => z) l (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hOne : Filter.Tendsto (fun z : Complex => rho + z) l (nhds rho) := by
    simpa only [add_zero] using tendsto_const_nhds.add hz
  have hTwo : Filter.Tendsto (fun z : Complex => rho + 2 * z) l (nhds rho) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
  have hThree : Filter.Tendsto (fun z : Complex => rho + 3 * z) l (nhds rho) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
  have hLimit : Filter.Tendsto
      (fun z : Complex =>
        C * (g (rho + z) * g (rho + 3 * z) ^ 3 / g (rho + 2 * z) ^ 4))
      l (nhds (C * (g rho * g rho ^ 3 / g rho ^ 4))) :=
    tendsto_const_nhds.mul
      (((hg.tendsto.comp hOne).mul ((hg.tendsto.comp hThree).pow 3)).div
        ((hg.tendsto.comp hTwo).pow 4) (pow_ne_zero 4 hg0))
  have hZero : Filter.Eventually (fun z : Complex => Not (z = 0)) l := by
    have hMem : Filter.Eventually
        (fun z : Complex => Membership.mem (Set.compl {0}) z) l :=
      self_mem_nhdsWithin
    apply hMem.mono
    intro z h he
    apply h
    rw [he]
    exact Set.mem_singleton 0
  have hNear := (hOne.eventually hfg).and
    ((hTwo.eventually hfg).and
      ((hThree.eventually hfg).and
        ((hTwo.eventually (hg.eventually_ne hg0)).and hZero)))
  have hEq : Filter.EventuallyEq l
      (fun z : Complex =>
        f (rho + z) * f (rho + 3 * z) ^ 3 / f (rho + 2 * z) ^ 4)
      (fun z : Complex =>
        C * (g (rho + z) * g (rho + 3 * z) ^ 3 / g (rho + 2 * z) ^ 4)) := by
    apply hNear.mono
    intro z h
    change f (rho + z) * f (rho + 3 * z) ^ 3 / f (rho + 2 * z) ^ 4 =
      C * (g (rho + z) * g (rho + 3 * z) ^ 3 / g (rho + 2 * z) ^ 4)
    rw [h.1, h.2.1, h.2.2.1]
    have hSubOne : rho + z - rho = z := by ring
    have hSubTwo : rho + 2 * z - rho = 2 * z := by ring
    have hSubThree : rho + 3 * z - rho = 3 * z := by ring
    rw [hSubOne, hSubThree, hSubTwo]
    dsimp [C]
    simp only [mul_pow]
    field_simp [pow_ne_zero m h.2.2.2.2,
      pow_ne_zero m (by norm_num : Not ((2 : Complex) = 0)), h.2.2.2.1]
  have hPowerThree : ((3 : Complex) ^ m) ^ 3 = ((3 : Complex) ^ 3) ^ m := by
    simp only [<- pow_mul, Nat.mul_comm m 3]
  have hPowerTwo : ((2 : Complex) ^ m) ^ 4 = ((2 : Complex) ^ 4) ^ m := by
    simp only [<- pow_mul, Nat.mul_comm m 4]
  have hC : C = (27 / 16 : Complex) ^ m := by
    dsimp [C]
    rw [hPowerThree, hPowerTwo, <- div_pow]
    norm_num
  have hCancel : g rho * g rho ^ 3 / g rho ^ 4 = 1 := by
    field_simp [hg0]
  have hConst : C * (g rho * g rho ^ 3 / g rho ^ 4) = (27 / 16 : Complex) ^ m := by
    rw [hCancel, mul_one, hC]
  rw [hConst] at hLimit
  exact (Filter.tendsto_congr' hEq).mpr hLimit

end Complex
