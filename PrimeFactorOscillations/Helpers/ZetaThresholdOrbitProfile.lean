/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityStability
import PrimeFactorOscillations.Helpers.ZetaReflectionMultiplicity

/-! # Reflection-paired finite profiles for actual zeta orders -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_finite_reflection_statistic_fold (W : Finset Complex) (t : Real)
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (phi : Real -> Real) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      phi ((w.re - 1 / 2) ^ 2 / t)) =
      2 * Finset.sum (W.filter (fun w => 1 / 2 < w.re))
        (fun w => (analyticOrderNatAt riemannZeta w : Real) * phi ((w.re - 1 / 2) ^ 2 / t)) +
      (Finset.sum (W.filter (fun w => w.re = 1 / 2))
        (fun w => (analyticOrderNatAt riemannZeta w : Real))) * phi 0 := by
  classical
  let L := W.filter (fun w => w.re < 1 / 2)
  let C := W.filter (fun w => w.re = 1 / 2)
  let R := W.filter (fun w => 1 / 2 < w.re)
  let f := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real) *
    phi ((w.re - 1 / 2) ^ 2 / t)
  have hSym : forall w, Membership.mem W w -> f (zetaHorizontalReflection w) = f w := by
    intro w hw
    dsimp only [f]
    rw [zetaOrder_reflection w (hStrip w hw), zetaHorizontalCoord_reflection, neg_sq]
  have hLR : Finset.sum L f = Finset.sum R f := by
    apply Finset.sum_bij (fun w _ => zetaHorizontalReflection w)
    case hi =>
      intro w hw
      have hm := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr
      refine And.intro (hReflect w hm.1) ?_
      rw [zetaHorizontalReflection_re]
      linarith only [hm.2]
    case i_inj =>
      intro a _ b _ hab
      exact zetaHorizontalReflection_injective hab
    case i_surj =>
      intro b hb
      have hm := Finset.mem_filter.mp hb
      have hMem : Membership.mem L (zetaHorizontalReflection b) := by
        apply Finset.mem_filter.mpr
        refine And.intro (hReflect b hm.1) ?_
        rw [zetaHorizontalReflection_re]
        linarith only [hm.2]
      exact Exists.intro (zetaHorizontalReflection b)
        (Exists.intro hMem (zetaHorizontalReflection_involutive b))
    case h =>
      intro w hw
      exact (hSym w (Finset.mem_filter.mp hw).1).symm
  have hPartition : Finset.sum W f = Finset.sum L f + Finset.sum C f + Finset.sum R f := by
    calc
      _ = Finset.sum W (fun w =>
          (if w.re < 1 / 2 then f w else 0) +
          (if w.re = 1 / 2 then f w else 0) +
          (if 1 / 2 < w.re then f w else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hL : w.re < 1 / 2
        case pos =>
          have hC : Not (w.re = 1 / 2) := ne_of_lt hL
          have hR : Not (1 / 2 < w.re) := not_lt.mpr hL.le
          simp only [ite_eq_left hL, ite_eq_right hC, ite_eq_right hR, add_zero]
        case neg =>
          by_cases hC : w.re = 1 / 2
          case pos => simp [hC]
          case neg =>
            have hR : 1 / 2 < w.re := lt_of_le_of_ne (le_of_not_gt hL) (Ne.symm hC)
            simp only [ite_eq_right hL, ite_eq_right hC, ite_eq_left hR, zero_add]
      _ = _ := by
        simp only [L, C, R, Finset.sum_filter, Finset.sum_add_distrib]
  have hCenter : Finset.sum C f =
      (Finset.sum C (fun w => (analyticOrderNatAt riemannZeta w : Real))) * phi 0 := by
    calc
      _ = Finset.sum C (fun w => (analyticOrderNatAt riemannZeta w : Real) * phi 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hc : w.re = 1 / 2 := (Finset.mem_filter.mp hw).2
        simp [f, hc]
      _ = _ := (Finset.sum_mul C (fun w => (analyticOrderNatAt riemannZeta w : Real)) (phi 0)).symm
  change Finset.sum W f = 2 * Finset.sum R f +
    (Finset.sum C (fun w => (analyticOrderNatAt riemannZeta w : Real))) * phi 0
  rw [hPartition, hLR, hCenter]
  ring


theorem zeta_finite_reflection_profile (W : Finset Complex) (t : Real) (ht : 0 < t)
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    exists n : Nat, exists a : Fin n -> Nat, exists y : Fin n -> Real,
      And (forall i, 0 <= y i)
        (And (forall i, exists w : Complex, And (Membership.mem W w)
          (And (1 / 2 < w.re) (And (a i = analyticOrderNatAt riemannZeta w)
            (y i = (w.re - 1 / 2) ^ 2 / t))))
          (forall phi : Real -> Real,
            Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
              phi ((w.re - 1 / 2) ^ 2 / t)) =
              Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) +
              (Finset.sum (W.filter (fun w => w.re = 1 / 2))
                (fun w => (analyticOrderNatAt riemannZeta w : Real))) * phi 0)) := by
  classical
  let R := W.filter (fun w => 1 / 2 < w.re)
  let e := R.equivFin
  let a := fun i : Fin R.card => analyticOrderNatAt riemannZeta (e.symm i).val
  let y := fun i : Fin R.card => ((e.symm i).val.re - 1 / 2) ^ 2 / t
  have hSum (f : Complex -> Real) :
      Finset.sum Finset.univ (fun i : Fin R.card => f (e.symm i).val) = Finset.sum R f := by
    exact (Equiv.sum_comp e.symm (fun w : R => f w.val)).trans (Finset.sum_coe_sort R f)
  refine Exists.intro R.card (Exists.intro a (Exists.intro y (And.intro ?hy (And.intro ?hc ?hs))))
  case hy =>
    intro i
    exact div_nonneg (sq_nonneg _) ht.le
  case hc =>
    intro i
    have hm := Finset.mem_filter.mp (e.symm i).property
    exact Exists.intro (e.symm i).val (And.intro hm.1 (And.intro hm.2 (And.intro rfl rfl)))
  case hs =>
    intro phi
    have hRight : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) =
        2 * Finset.sum R (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          phi ((w.re - 1 / 2) ^ 2 / t)) := by
      calc
        _ = 2 * Finset.sum Finset.univ (fun i : Fin R.card =>
            (analyticOrderNatAt riemannZeta (e.symm i).val : Real) *
              phi (((e.symm i).val.re - 1 / 2) ^ 2 / t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [a, y]
          ring
        _ = _ := congrArg (fun q : Real => 2 * q)
          (hSum (fun w : Complex => (analyticOrderNatAt riemannZeta w : Real) *
            phi ((w.re - 1 / 2) ^ 2 / t)))
    rw [hRight]
    exact zeta_finite_reflection_statistic_fold W t hStrip hReflect phi
end PrimeFactorOscillations
