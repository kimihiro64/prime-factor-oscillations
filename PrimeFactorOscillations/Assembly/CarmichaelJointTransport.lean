/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelStripGeometry

/-!
# Coupled transport of common weak zeta multiplicities

Both compensation rows are retained. The transported common-weak mass is
bounded by the right-half mass and by its affine e/d transport. Its finite
sum is exactly e times the original common-weak multiplicity mass.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelStripCarrier

open DirichletCompensatedProbe CarmichaelWeightedSignal

def jointWeakSupport (d e T : Real) : Finset Complex :=
  (upperZeroValues T).filter (fun z =>
    (analyticOrderNatAt riemannZeta z : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real) /\
    (analyticOrderNatAt riemannZeta z : Real) <=
      e * (analyticOrderNatAt riemannZeta (powerMap e z) : Real))

def jointWeakLift (d e T : Real) (z : Complex) : Real :=
  if Membership.mem (jointWeakSupport d e T) (powerSource e z) then
    e * zetaSquareMass (powerSource e z) else 0

theorem weak_reference_window (d T : Real) (hd : 2 <= d) (z : Complex)
    (hz : zetaZeroWindow T z)
    (hWeak : (analyticOrderNatAt riemannZeta z : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real)) :
    zetaZeroWindow T (powerMap d z) /\ (1 / 2 : Real) < (powerMap d z).re := by
  have hSource : 0 < (analyticOrderNatAt riemannZeta z : Real) := by
    exact_mod_cast zeta_order_pos_of_window T z hz
  have hRef : 0 < analyticOrderNatAt riemannZeta (powerMap d z) := by
    by_contra hNot
    have hZero := Nat.eq_zero_of_not_pos hNot
    simp only [hZero, Nat.cast_zero, mul_zero] at hWeak
    exact (not_le_of_gt hSource) hWeak
  exact powerMap_window d T hd z hz hRef

theorem weak_source_mass_le_reference (d T : Real) (hd : 0 < d) (z : Complex)
    (hz : zetaZeroWindow T z)
    (hWeak : (analyticOrderNatAt riemannZeta z : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real)) :
    d * zetaSquareMass z <= zetaSquareMass (powerMap d z) := by
  have hi : (powerMap d z).im = z.im / d :=
    (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd z)
  have hWeight : 0 <= d / z.im ^ 2 := div_nonneg hd.le (sq_nonneg _)
  unfold zetaSquareMass zetaWeightedMultiplicity
  rw [hi]
  calc
    d * ((analyticOrderNatAt riemannZeta z : Real) * (1 / z.im ^ 2)) =
        (d / z.im ^ 2) * (analyticOrderNatAt riemannZeta z : Real) := by ring
    _ <= (d / z.im ^ 2) *
        (d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real)) :=
      mul_le_mul_of_nonneg_left hWeak hWeight
    _ = (analyticOrderNatAt riemannZeta (powerMap d z) : Real) *
        (1 / (z.im / d) ^ 2) := by
      field_simp [hd.ne', (ne_of_gt hz.2.2.2.1)]

theorem jointWeak_reference_mem_right (d e T : Real) (he : 2 <= e) (z : Complex)
    (hz : Membership.mem (jointWeakSupport d e T) z) :
    Membership.mem (rightZeroSupport T) (powerMap e z) := by
  have h := Finset.mem_filter.mp hz
  have hRef := weak_reference_window e T he z
    ((mem_upperZeroValues T z).mp h.1) h.2.2
  exact Finset.mem_filter.mpr
    (And.intro ((mem_upperZeroValues T _).mpr hRef.1) hRef.2)

theorem jointWeakLift_nonneg (d e T : Real) (he : 0 <= e) (z : Complex) :
    0 <= jointWeakLift d e T z := by
  unfold jointWeakLift
  split_ifs
  . exact mul_nonneg he (zetaSquareMass_nonneg _)
  . exact le_rfl

theorem jointWeakLift_le_rightMass (d e T : Real) (he : 2 <= e) (z : Complex) :
    jointWeakLift d e T z <= rightZeroMass T z := by
  have he0 : 0 < e := by linarith
  by_cases hs : Membership.mem (jointWeakSupport d e T) (powerSource e z)
  . have h := Finset.mem_filter.mp hs
    have hRight := jointWeak_reference_mem_right d e T he (powerSource e z) hs
    rw [powerMap_powerSource e he0 z] at hRight
    have hMass := weak_source_mass_le_reference e T he0 (powerSource e z)
      ((mem_upperZeroValues T _).mp h.1) h.2.2
    rw [powerMap_powerSource e he0 z] at hMass
    simpa only [jointWeakLift, ite_eq_left hs, rightZeroMass, ite_eq_left hRight]
      using hMass
  . simpa only [jointWeakLift, ite_eq_right hs] using rightZeroMass_nonneg T z

theorem jointWeakLift_transport (d e T : Real) (hd : 2 <= d) (he : 2 <= e)
    (z : Complex) :
    jointWeakLift d e T z <= (e / d) * rightZeroMass T (stripTransport (e / d) z) := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hr : 0 <= e / d := div_nonneg he0.le hd0.le
  by_cases hs : Membership.mem (jointWeakSupport d e T) (powerSource e z)
  . have h := Finset.mem_filter.mp hs
    have hWindow := (mem_upperZeroValues T _).mp h.1
    have hRef := weak_reference_window d T hd (powerSource e z) hWindow h.2.1
    have hRight : Membership.mem (rightZeroSupport T)
        (powerMap d (powerSource e z)) := Finset.mem_filter.mpr
      (And.intro ((mem_upperZeroValues T _).mpr hRef.1) hRef.2)
    rw [powerMap_powerSource_eq_transport d e hd0 z] at hRight
    have hMass := weak_source_mass_le_reference d T hd0 (powerSource e z)
      hWindow h.2.1
    rw [powerMap_powerSource_eq_transport d e hd0 z] at hMass
    have hCancel : (e / d) * (d * zetaSquareMass (powerSource e z)) =
        e * zetaSquareMass (powerSource e z) := by
      field_simp
    have hScaled := mul_le_mul_of_nonneg_left hMass hr
    rw [hCancel] at hScaled
    simpa only [jointWeakLift, ite_eq_left hs, rightZeroMass, ite_eq_left hRight]
      using hScaled
  . simpa only [jointWeakLift, ite_eq_right hs] using
      mul_nonneg hr (rightZeroMass_nonneg T (stripTransport (e / d) z))

theorem jointWeakLift_support (d e T : Real) (he : 2 <= e) (z : Complex)
    (hz : Not (Membership.mem (rightZeroSupport T) z)) :
    jointWeakLift d e T z = 0 := by
  have h := jointWeakLift_le_rightMass d e T he z
  rw [rightZeroMass_support T z hz] at h
  exact le_antisymm h (jointWeakLift_nonneg d e T (by linarith) z)

theorem jointWeakLift_at_reference (d e T : Real) (he : 0 < e)
    (z : Complex) (hz : Membership.mem (jointWeakSupport d e T) z) :
    jointWeakLift d e T (powerMap e z) = e * zetaSquareMass z := by
  simp only [jointWeakLift, powerSource_powerMap e he z, ite_eq_left hz]

theorem jointWeakLift_sum (d e T : Real) (he : 2 <= e) :
    (rightZeroSupport T).sum (jointWeakLift d e T) =
      e * (jointWeakSupport d e T).sum zetaSquareMass := by
  classical
  have he0 : 0 < e := by linarith
  let U := jointWeakSupport d e T
  let Q := U.image (powerMap e)
  let R := rightZeroSupport T
  have hSubset : Q <= R := by
    intro z hz
    choose rho hr heq using Finset.mem_image.mp hz
    rw [<- heq]
    exact jointWeak_reference_mem_right d e T he rho hr
  have hOff : forall z, Membership.mem R z -> Not (Membership.mem Q z) ->
      jointWeakLift d e T z = 0 := by
    intro z hz hNot
    by_cases hs : Membership.mem U (powerSource e z)
    . exfalso
      exact hNot (Finset.mem_image.mpr (Exists.intro (powerSource e z)
        (And.intro hs (powerMap_powerSource e he0 z))))
    . change Not (Membership.mem (jointWeakSupport d e T) (powerSource e z)) at hs
      simp only [jointWeakLift, ite_eq_right hs]
  have hRestrict : Q.sum (jointWeakLift d e T) = R.sum (jointWeakLift d e T) :=
    Finset.sum_subset hSubset hOff
  calc
    _ = Q.sum (jointWeakLift d e T) := hRestrict.symm
    _ = U.sum (fun z => e * zetaSquareMass z) := by
      dsimp only [Q]
      rw [Finset.sum_image (fun x _ y _ hxy => powerMap_injective e he0 hxy)]
      apply Finset.sum_congr rfl
      intro z hz
      exact jointWeakLift_at_reference d e T he0 z hz
    _ = e * U.sum zetaSquareMass := (Finset.mul_sum _ _ _).symm

theorem rightZeroMass_sum (T : Real) :
    (rightZeroSupport T).sum (rightZeroMass T) =
      (rightZeroSupport T).sum zetaSquareMass := by
  apply Finset.sum_congr rfl
  intro z hz
  exact ite_eq_left hz

end PrimeFactorOscillations.CarmichaelStripCarrier
