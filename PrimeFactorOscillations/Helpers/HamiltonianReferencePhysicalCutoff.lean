/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalReferenceSeparation

/-! # Grid-independent physical leakage bounds

The separated-center radius is floor(R/(4 Q^2)). Its reciprocal bound is
at most 4 Q^2, with all integer rounding and small endpoint conditions
retained. The wide minor complement is contained in the original narrow
minor complement. No auxiliary grid cardinality enters either bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_rational_grid_mono (R Q W T : Nat) (hWT : W <= T) :
    lpfRationalGrid R Q W <= lpfRationalGrid R Q T := by
  intro x hx
  choose u hu hEq using Finset.mem_image.mp hx
  have hBounds := Finset.mem_Icc.mp (Finset.mem_product.mp hu).2
  have hWTi : (W : Int) <= (T : Int) := by exact_mod_cast hWT
  apply Finset.mem_image.mpr
  refine Exists.intro u (And.intro ?_ hEq)
  apply Finset.mem_product.mpr
  exact And.intro (Finset.mem_univ _) (Finset.mem_Icc.mpr
    (And.intro (by omega) (by omega)))

theorem hamiltonian_reference_physical_radius {R : Nat} [NeZero R]
    (M Q T : Nat) (hM : 0 < M) (hQ : 0 < Q) (hT : 0 < T)
    (hDiv : Dvd.dvd M R) (hRange : 4 * T * Q ^ 2 <= M) :
    let W := (R / M) * T
    let D := R / (4 * Q ^ 2)
    And (1 <= W) (And (W <= D)
      (And (2 * D * Q ^ 2 < R)
        ((R : Real) / (2 * (D : Real)) <= 4 * (Q : Real) ^ 2))) := by
  let B := R / M
  let W := B * T
  let D := R / (4 * Q ^ 2)
  have hR : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  have hB : 0 < B := Nat.div_pos (Nat.le_of_dvd hR hDiv) hM
  have hFactor : B * M = R := Nat.div_mul_cancel hDiv
  have hDen : 0 < 4 * Q ^ 2 := by positivity
  have hW : 1 <= W := Nat.mul_pos hB hT
  have hProd : W * (4 * Q ^ 2) <= R := by
    have h := Nat.mul_le_mul_left B hRange
    dsimp [W]
    nlinarith only [h, hFactor]
  have hWD : W <= D := (Nat.le_div_iff_mul_le hDen).mpr hProd
  have hD : 1 <= D := hW.trans hWD
  have hUpper : D * (4 * Q ^ 2) <= R := Nat.div_mul_le_self R (4 * Q ^ 2)
  have hWidth : 2 * D * Q ^ 2 < R := by nlinarith only [hUpper, hR]
  have hMod : R % (4 * Q ^ 2) < 4 * Q ^ 2 := Nat.mod_lt R hDen
  have hDivision : R % (4 * Q ^ 2) + (4 * Q ^ 2) * D = R := Nat.mod_add_div R _
  have hLower : R <= 8 * D * Q ^ 2 := by
    have hDProduct := Nat.mul_le_mul_right (4 * Q ^ 2) hD
    nlinarith only [hMod, hDivision, hDProduct]
  have hReal : (R : Real) <= (4 * (Q : Real) ^ 2) * (2 * (D : Real)) := by
    have h : (R : Real) <= 8 * (D : Real) * (Q : Real) ^ 2 := by
      exact_mod_cast hLower
    nlinarith only [h]
  have hDR : (0 : Real) < (D : Real) := by exact_mod_cast (show 0 < D by omega)
  have hReciprocal : (R : Real) / (2 * (D : Real)) <= 4 * (Q : Real) ^ 2 := by
    calc
      _ <= ((4 * (Q : Real) ^ 2) * (2 * (D : Real))) / (2 * (D : Real)) :=
        div_le_div_of_nonneg_right hReal (by positivity)
      _ = _ := by field_simp
  exact And.intro hW (And.intro hWD (And.intro hWidth hReciprocal))

theorem hamiltonian_reference_scaled_far_bound {R : Nat} [NeZero R]
    (M Q T s L : Nat) (hM : 0 < M) (hT : 0 < T) (hDiv : Dvd.dvd M R)
    (x : ZMod R)
    (hx : Not (Membership.mem (lpfRationalGrid R Q ((R / M) * T)) x)) :
    norm (hamiltonianFullRationalReference R Q s L x) <=
      (Q : Real) * ((M : Real) / (2 * (T : Real))) := by
  have hR : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  have hB : 0 < R / M := Nat.div_pos (Nat.le_of_dvd hR hDiv) hM
  have hW : 1 <= (R / M) * T := Nat.mul_pos hB hT
  have hFactor : (R : Real) = ((R / M : Nat) : Real) * (M : Real) := by
    exact_mod_cast (Nat.div_mul_cancel hDiv).symm
  have hBR : (0 : Real) < ((R / M : Nat) : Real) := by exact_mod_cast hB
  have hTR : (0 : Real) < (T : Real) := by exact_mod_cast hT
  have hEq : (R : Real) / (2 * (((R / M) * T : Nat) : Real)) =
      (M : Real) / (2 * (T : Real)) := by
    rw [hFactor, Nat.cast_mul]
    field_simp
  have h := hamiltonian_full_reference_far_bound Q s L ((R / M) * T) hW x
    (hamiltonian_outside_rational_grid_far Q ((R / M) * T) x hx)
  rwa [hEq] at h

end PrimeFactorOscillations.LPF
