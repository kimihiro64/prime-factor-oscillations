/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineWindowProfile
import PrimeFactorOscillations.Helpers.XiClusterMultiplicity

/-! # Full multiplicity transport with the exact physical-window charge -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

theorem xi_exact_window_finite_mass (T h : Real) (h0 : 0 <= h) (hMax : h <= 3 / 20)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (S : Finset RiemannXiDivisorZeroIndex)
    (hWindow : forall p, Membership.mem S p -> abs (T - (riemannXiDivisorZeroValue p).im) <= h) :
    Finset.sum S (fun _ => threeLineExactWindowCharge h) <= threeLineXiTrace T := by
  have hLocal : Finset.sum S (fun _ => threeLineExactWindowCharge h) <=
      Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (T - (riemannXiDivisorZeroValue p).im)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact threeLineKernel_rectangle_min h _ _ h0 hMax (hStrip p) (hWindow p hp)
  exact hLocal.trans (xi_threeLine_finite_mass T hStrip S)

theorem zeta_finite_exact_window_charge_trace (T h : Real) (h0 : 0 <= h) (hMax : h <= 3 / 20)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= h)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      threeLineExactWindowCharge h) <= threeLineXiTrace T := by
  classical
  have hw0 (w : Complex) (hw : Membership.mem W w) : Not (w = 0) := by
    intro he
    have hh := (hCritical w hw).1
    rw [he] at hh
    norm_num at hh
  have hIndices : forall p, Membership.mem (xiFiniteMultiplicityUnion W) p ->
      abs (T - (riemannXiDivisorZeroValue p).im) <= h := by
    intro p hp
    change Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p at hp
    choose w hw hpf using Finset.mem_biUnion.mp hp
    have hv := (xiFiniteMultiplicityFiber_mem w (hw0 w hw) p).mp hpf
    rw [hv]
    exact hWindow w hw
  rw [zeta_finite_multiplicity_transport W hCritical]
  exact xi_exact_window_finite_mass T h h0 hMax hStrip _ hIndices

end PrimeFactorOscillations
