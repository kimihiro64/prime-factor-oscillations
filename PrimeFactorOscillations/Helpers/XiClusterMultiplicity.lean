/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineClusterCertificate
import PrimeFactorOscillations.Helpers.XiHorizontalMultiplicity

/-! # Full signed multiplicity-fiber transport for arbitrary finite zero clusters -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def xiFiniteMultiplicityUnion (W : Finset Complex) : Finset RiemannXiDivisorZeroIndex := by
  classical
  exact W.biUnion xiFiniteMultiplicityFiber

theorem zeta_finite_multiplicity_transport (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (F : Complex -> Real) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * F w) =
      Finset.sum (xiFiniteMultiplicityUnion W)
        (fun p => F (riemannXiDivisorZeroValue p)) := by
  classical
  unfold xiFiniteMultiplicityUnion
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
  have hFiber (w : Complex) (hw : Membership.mem W w) :
      Finset.sum (xiFiniteMultiplicityFiber w) (fun p => F (riemannXiDivisorZeroValue p)) =
        (analyticOrderNatAt riemannZeta w : Real) * F w := by
    have hw1 : Not (w = 1) := by
      intro he
      have hh := (hCritical w hw).2
      rw [he] at hh
      norm_num at hh
    calc
      _ = Finset.sum (xiFiniteMultiplicityFiber w) (fun _ => F w) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(xiFiniteMultiplicityFiber_mem w (hw0 w hw) p).mp hp]
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, xiFiniteMultiplicityFiber_card w (hw0 w hw),
          xiZeroMultiplicity_eq_zetaOrder (hCritical w hw).1 hw1]
  calc
    _ = Finset.sum W (fun w => Finset.sum (xiFiniteMultiplicityFiber w)
        (fun p => F (riemannXiDivisorZeroValue p))) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (hFiber w hw).symm
    _ = _ := (Finset.sum_biUnion hDisjoint).symm

theorem xi_threeLine_finite_cluster_charge (T : Real)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (S : Finset RiemannXiDivisorZeroIndex) :
    Finset.sum S (fun p => threeLineCharge + (13 / 2 : Real) *
      ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 -
        48 * (T - (riemannXiDivisorZeroValue p).im) ^ 2) <= threeLineXiTrace T := by
  have hLocal : Finset.sum S (fun p => threeLineCharge + (13 / 2 : Real) *
      ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 -
        48 * (T - (riemannXiDivisorZeroValue p).im) ^ 2) <=
      Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (T - (riemannXiDivisorZeroValue p).im)) := by
    apply Finset.sum_le_sum
    intro p _
    exact threeLineKernel_cluster_charge _ _ (hStrip p)
  exact hLocal.trans (xi_threeLine_finite_mass T hStrip S)

theorem zeta_finite_cluster_charge_trace (T : Real) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2 -
        48 * (T - w.im) ^ 2)) <= threeLineXiTrace T := by
  rw [zeta_finite_multiplicity_transport W hCritical]
  exact xi_threeLine_finite_cluster_charge T hStrip _

end PrimeFactorOscillations
