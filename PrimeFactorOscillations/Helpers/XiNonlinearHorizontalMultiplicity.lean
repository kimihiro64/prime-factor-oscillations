/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineHorizontalConvexity
import PrimeFactorOscillations.Helpers.XiClusterMultiplicity

/-! # Joint nonlinear horizontal charging with every multiplicity copy retained -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

theorem zeta_finite_horizontal_nonlinear_charge_trace (t : Real) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (z : Real) (hN : 0 < Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real)))
    (hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (w.re - 1 / 2) ^ 2) =
        Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real)) * z) :
    And (And (0 <= z) (z <= 9 / 64))
      (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real)) *
        threeLineHorizontalProfile z + threeLineHorizontalVarianceCoefficient *
          Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
            ((w.re - 1 / 2) ^ 2 - z) ^ 2) <= threeLineXiTrace t) := by
  classical
  let S := xiFiniteMultiplicityUnion W
  let x : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  have hCard : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real)) =
      (S.card : Real) := by
    have h := zeta_finite_multiplicity_transport W hCritical (fun _ => (1 : Real))
    change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * 1) =
      Finset.sum S (fun _ => (1 : Real)) at h
    simpa only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have hMoment := zeta_finite_multiplicity_transport W hCritical
    (fun w => (w.re - 1 / 2) ^ 2)
  change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
    (w.re - 1 / 2) ^ 2) = Finset.sum S x at hMoment
  have hVariance := zeta_finite_multiplicity_transport W hCritical
    (fun w => ((w.re - 1 / 2) ^ 2 - z) ^ 2)
  change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
    ((w.re - 1 / 2) ^ 2 - z) ^ 2) = Finset.sum S (fun p => (x p - z) ^ 2) at hVariance
  have hx (p : RiemannXiDivisorZeroIndex) (_hp : Membership.mem S p) :
      And (0 <= x p) (x p <= 9 / 64) := by
    have hu := abs_le.mp (hStrip p)
    have hPlus : 0 <= ((riemannXiDivisorZeroValue p).re - 1 / 2) + 3 / 8 := by
      linarith [hu.1]
    have hProduct := mul_nonneg (sub_nonneg.mpr hu.2) hPlus
    constructor
    case left => exact sq_nonneg _
    case right => dsimp only [x]; nlinarith
  have hCenterS : Finset.sum S x = (S.card : Real) * z := by
    rw [<- hMoment, <- hCard]
    exact hCenter
  have hNS : 0 < (S.card : Real) := by rw [<- hCard]; exact hN
  have hz := threeLineHorizontal_mean_bounds S x z hx hNS hCenterS
  have hSameS (p : RiemannXiDivisorZeroIndex) (hp : Membership.mem S p) :
      (riemannXiDivisorZeroValue p).im = t := by
    change Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p at hp
    choose w hw hpf using Finset.mem_biUnion.mp hp
    have hw0 : Not (w = 0) := by
      intro he
      have h := (hCritical w hw).1
      rw [he] at h
      norm_num at h
    have hv := (xiFiniteMultiplicityFiber_mem w hw0 p).mp hpf
    rw [hv]
    exact hSame w hw
  have hKernel : Finset.sum S (fun p => threeLineHorizontalProfile (x p)) =
      Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (t - (riemannXiDivisorZeroValue p).im)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hSameS p hp, sub_self, threeLineKernel_horizontal_profile _ (hStrip p)]
  have hLocal := threeLineHorizontal_centered_charge S x z hx hz hCenterS
  rw [<- hCard, <- hVariance] at hLocal
  have hUpper : Finset.sum S (fun p => threeLineHorizontalProfile (x p)) <=
      threeLineXiTrace t := by
    rw [hKernel]
    exact xi_threeLine_finite_mass t hStrip S
  exact And.intro hz (hLocal.trans hUpper)

end PrimeFactorOscillations
