/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineHorizontalCharge
import PrimeFactorOscillations.Helpers.XiThreeLineMultiplicity

/-! # Joint multiplicity and horizontal-spread charging at a common ordinate -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def xiFiniteMultiplicityFiber (w : Complex) : Finset RiemannXiDivisorZeroIndex := by
  classical
  exact if hw0 : w = 0 then Finset.empty else
    Finset.univ.image (fun k : Fin (xiZeroMultiplicity w) =>
      ((xiZeroFiberEquiv w hw0).symm k).val)

theorem xiFiniteMultiplicityFiber_mem (w : Complex) (hw0 : Not (w = 0))
    (p : RiemannXiDivisorZeroIndex) :
    Membership.mem (xiFiniteMultiplicityFiber w) p <-> riemannXiDivisorZeroValue p = w := by
  classical
  let e := xiZeroFiberEquiv w hw0
  unfold xiFiniteMultiplicityFiber
  rw [dite_eq_right hw0]
  change Membership.mem (Finset.univ.image
    (fun k : Fin (xiZeroMultiplicity w) => (e.symm k).val)) p <-> _
  constructor
  case mp =>
    intro hp
    choose k _ hkp using Finset.mem_image.mp hp
    rw [<- hkp]
    exact (e.symm k).property
  case mpr =>
    intro hp
    apply Finset.mem_image.mpr
    exact Exists.intro (e (Subtype.mk p hp)) (And.intro (Finset.mem_univ _)
      (congrArg Subtype.val (e.symm_apply_apply (Subtype.mk p hp))))

theorem xiFiniteMultiplicityFiber_card (w : Complex) (hw0 : Not (w = 0)) :
    (xiFiniteMultiplicityFiber w).card = xiZeroMultiplicity w := by
  classical
  let e := xiZeroFiberEquiv w hw0
  let j : Fin (xiZeroMultiplicity w) -> RiemannXiDivisorZeroIndex :=
    fun k => (e.symm k).val
  have hj : Function.Injective j := by
    intro a b h
    apply e.symm.injective
    exact Subtype.ext h
  unfold xiFiniteMultiplicityFiber
  rw [dite_eq_right hw0]
  change (Finset.univ.image j).card = _
  rw [Finset.card_image_of_injective _ hj]
  simp

theorem xi_threeLine_finite_horizontal_charge (t : Real)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (S : Finset RiemannXiDivisorZeroIndex)
    (hSame : forall p, Membership.mem S p -> (riemannXiDivisorZeroValue p).im = t) :
    Finset.sum S (fun p => threeLineCharge + (13 / 2 : Real) *
      ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2) <= threeLineXiTrace t := by
  have hLocal : Finset.sum S (fun p => threeLineCharge + (13 / 2 : Real) *
      ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2) <=
      Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (t - (riemannXiDivisorZeroValue p).im)) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [hSame p hp, sub_self]
    exact threeLineKernel_quadratic_charge _ ((hStrip p).trans (by norm_num))
  exact hLocal.trans (xi_threeLine_finite_mass t hStrip S)

theorem zeta_finite_horizontal_charge_trace (t : Real) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2)) <= threeLineXiTrace t := by
  classical
  have hw0 (w : Complex) (hw : Membership.mem W w) : Not (w = 0) := by
    intro he
    have hh := (hCritical w hw).1
    rw [he] at hh
    norm_num at hh
  have hDisjoint : (W : Set Complex).PairwiseDisjoint xiFiniteMultiplicityFiber := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have hA := (xiFiniteMultiplicityFiber_mem a (hw0 a ha) p).mp hpa
    have hB := (xiFiniteMultiplicityFiber_mem b (hw0 b hb) p).mp hpb
    exact hab (hA.symm.trans hB)
  let cost : RiemannXiDivisorZeroIndex -> Real := fun p =>
    threeLineCharge + (13 / 2 : Real) * ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  have hFiber (w : Complex) (hw : Membership.mem W w) :
      Finset.sum (xiFiniteMultiplicityFiber w) cost =
        (analyticOrderNatAt riemannZeta w : Real) *
          (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2) := by
    have hw1 : Not (w = 1) := by
      intro he
      have hh := (hCritical w hw).2
      rw [he] at hh
      norm_num at hh
    calc
      _ = Finset.sum (xiFiniteMultiplicityFiber w) (fun _ =>
          threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hv := (xiFiniteMultiplicityFiber_mem w (hw0 w hw) p).mp hp
        dsimp only [cost]
        rw [hv]
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, xiFiniteMultiplicityFiber_card w (hw0 w hw),
          xiZeroMultiplicity_eq_zetaOrder (hCritical w hw).1 hw1]
  have hAll : forall p, Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p ->
      (riemannXiDivisorZeroValue p).im = t := by
    intro p hp
    choose w hw hpf using Finset.mem_biUnion.mp hp
    have hv := (xiFiniteMultiplicityFiber_mem w (hw0 w hw) p).mp hpf
    rw [hv]
    exact hSame w hw
  calc
    _ = Finset.sum W (fun w => Finset.sum (xiFiniteMultiplicityFiber w) cost) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (hFiber w hw).symm
    _ = Finset.sum (W.biUnion xiFiniteMultiplicityFiber) cost :=
      (Finset.sum_biUnion hDisjoint).symm
    _ <= _ := xi_threeLine_finite_horizontal_charge t hStrip _ hAll

theorem zeta_multiplicity_horizontal_charge_trace {w : Complex}
    (hw : And (0 < w.re) (w.re < 1))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    (analyticOrderNatAt riemannZeta w : Real) *
      (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2) <= threeLineXiTrace w.im := by
  have h := zeta_finite_horizontal_charge_trace w.im (({w} : Finset Complex))
    (fun z hz => by
      have he : z = w := Finset.mem_singleton.mp hz
      subst z
      exact hw)
    (fun z hz => by
      have he : z = w := Finset.mem_singleton.mp hz
      subst z
      rfl) hStrip
  simpa only [Finset.sum_singleton] using h

end PrimeFactorOscillations
