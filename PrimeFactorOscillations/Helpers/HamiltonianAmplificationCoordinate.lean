/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantNormalization

/-! # Sharp spectral amplification coordinate

Convexity of log(1+x)-log(1-x) supplies the exact chord coefficient.
This is the coefficient consumed by the logarithmic-density count.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianAmplificationCoordinate (x : Real) : Real :=
  Real.log (1 + x) - Real.log (1 - x)

theorem hamiltonian_amplification_coordinate_derivative
    (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasDerivAt hamiltonianAmplificationCoordinate (2 / (1 - x ^ 2)) x := by
  have hPlus : 0 < 1 + x := by linarith only [hx]
  have hMinus : 0 < 1 - x := sub_pos.mpr hx1
  have hSquare : 0 < 1 - x ^ 2 := by nlinarith only [hx, hx1]
  have hp : HasDerivAt (fun y : Real => 1 + y) 1 x := by
    convert (hasDerivAt_id x).const_add 1 using 1 <;> first | rfl | ring
  have hm : HasDerivAt (fun y : Real => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : Real)).sub (hasDerivAt_id x) using 1 <;> first | rfl | ring
  have h := (hp.log (ne_of_gt hPlus)).sub (hm.log (ne_of_gt hMinus))
  unfold hamiltonianAmplificationCoordinate
  convert h using 1
  field_simp [ne_of_gt hPlus, ne_of_gt hMinus, ne_of_gt hSquare]
  <;> ring

theorem hamiltonian_amplification_derivative_monotone
    (x y : Real) (hx : 0 <= x) (hxy : x <= y) (hy : y < 1) :
    2 / (1 - x ^ 2) <= 2 / (1 - y ^ 2) := by
  have hy0 : 0 <= y := le_trans hx hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy
  have hX : 0 < 1 - x ^ 2 := by nlinarith only [hx, hx1]
  have hY : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy]
  have hSquares : x ^ 2 <= y ^ 2 := by nlinarith only [hx, hy0, hxy]
  have hClearX : (2 / (1 - x ^ 2)) * ((1 - x ^ 2) * (1 - y ^ 2)) =
      2 * (1 - y ^ 2) := by field_simp [ne_of_gt hX]
  have hClearY : (2 / (1 - y ^ 2)) * ((1 - x ^ 2) * (1 - y ^ 2)) =
      2 * (1 - x ^ 2) := by field_simp [ne_of_gt hY]
  apply le_of_mul_le_mul_right _ (mul_pos hX hY)
  rw [hClearX, hClearY]
  nlinarith only [hSquares]

theorem hamiltonian_amplification_coordinate_convex
    (r : Real) (hr : 0 <= r) (hr1 : r < 1) :
    ConvexOn Real (Set.Icc 0 r) hamiltonianAmplificationCoordinate := by
  have hBounds (x : Real) (hx : Membership.mem (Set.Icc 0 r) x) :
      0 <= x /\ x < 1 := And.intro hx.1 (lt_of_le_of_lt hx.2 hr1)
  have hContinuous : ContinuousOn hamiltonianAmplificationCoordinate (Set.Icc 0 r) := by
    intro x hx
    exact (hamiltonian_amplification_coordinate_derivative x
      (hBounds x hx).1 (hBounds x hx).2).continuousAt.continuousWithinAt
  have hDifferentiable :
      DifferentiableOn Real hamiltonianAmplificationCoordinate (interior (Set.Icc 0 r)) := by
    intro x hx
    have hb := hBounds x (interior_subset hx)
    exact (hamiltonian_amplification_coordinate_derivative x hb.1 hb.2).differentiableAt.differentiableWithinAt
  have hMonotone :
      MonotoneOn (deriv hamiltonianAmplificationCoordinate) (interior (Set.Icc 0 r)) := by
    intro x hx y hy hxy
    have hbX := hBounds x (interior_subset hx)
    have hbY := hBounds y (interior_subset hy)
    rw [(hamiltonian_amplification_coordinate_derivative x hbX.1 hbX.2).deriv,
      (hamiltonian_amplification_coordinate_derivative y hbY.1 hbY.2).deriv]
    exact hamiltonian_amplification_derivative_monotone x y hbX.1 hxy hbY.2
  exact hMonotone.convexOn_of_deriv (convex_Icc 0 r) hContinuous hDifferentiable

theorem hamiltonian_amplification_coordinate_chord
    (r x : Real) (hr : 0 < r) (hr1 : r < 1) (hx : 0 <= x) (hxr : x <= r) :
    hamiltonianAmplificationCoordinate x <=
      (hamiltonianAmplificationCoordinate r / r) * x := by
  have hConvex := hamiltonian_amplification_coordinate_convex r (le_of_lt hr) hr1
  have h0 : Membership.mem (Set.Icc 0 r) (0 : Real) := And.intro (le_refl _) (le_of_lt hr)
  have hR : Membership.mem (Set.Icc 0 r) r := And.intro (le_of_lt hr) (le_refl _)
  have hQuot : x / r <= 1 := by
    apply le_of_mul_le_mul_right _ hr
    have hClear : (x / r) * r = x := by field_simp [ne_of_gt hr]
    rw [hClear, one_mul]
    exact hxr
  have hLeft : 0 <= 1 - x / r := sub_nonneg.mpr hQuot
  have hRight : 0 <= x / r := div_nonneg hx (le_of_lt hr)
  have hSum : (1 - x / r) + x / r = 1 := by ring
  have h := hConvex.2 h0 hR hLeft hRight hSum
  simp only [smul_eq_mul] at h
  have hArgument : (1 - x / r) * 0 + x / r * r = x := by field_simp [ne_of_gt hr] <;> ring
  have hZero : hamiltonianAmplificationCoordinate 0 = 0 := by
    simp [hamiltonianAmplificationCoordinate]
  rw [hArgument, hZero, mul_zero, zero_add] at h
  calc
    _ <= x / r * hamiltonianAmplificationCoordinate r := h
    _ = _ := by ring

end PrimeFactorOscillations
