/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.UnramifiedBlock

/-!
# Torsion covariance of the finite tame Gauss block

A simultaneous cyclic translation accounts for both supports of a square
torsion twist. The complete finite block retains its energy bound on the
explicit conductor annulus. This file does not identify a global theta
transform or supply an analytic moment estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The entire tame block after a square torsion twist; neither support is omitted. -/
noncomputable def shiftedTameGaussBlock (kappa : MulChar F Complex)
    (psi : AddChar F Complex) (m : Nat) (z : Complex) (d i j : ZMod m) : Complex :=
  (if j = i - 1 then gaussSum (kappa ^ (2 * i - 1 - 2 * d).val) psi /
    ((Fintype.card F : Complex) * z) else 0) +
  (if j = 2 * d - i then
    ((1 - (Fintype.card F : Real) ^ (-1 : Int) : Real) : Complex) *
      z ^ (-2 * i + 2 * d).val / (1 - z ^ m) else 0)

/-- A simultaneous cyclic row/column permutation accounts for the entire twist. -/
theorem shiftedTameGaussBlock_eq_reindex (kappa : MulChar F Complex)
    (psi : AddChar F Complex) (m : Nat) (z : Complex) (d i j : ZMod m) :
    shiftedTameGaussBlock kappa psi m z d i j =
      shiftedTameGaussBlock kappa psi m z 0 (i - d) (j - d) := by
  have hfirst : j - d = (i - d) - 1 <-> j = i - 1 := by
    constructor
    . intro h
      calc
        j = (j - d) + d := by ring
        _ = ((i - d) - 1) + d := by rw [h]
        _ = i - 1 := by ring
    . intro h
      rw [h]
      ring
  have hsecond : j - d = -(i - d) <-> j = 2 * d - i := by
    constructor
    . intro h
      calc
        j = (j - d) + d := by ring
        _ = -(i - d) + d := by rw [h]
        _ = 2 * d - i := by ring
    . intro h
      rw [h]
      ring
  have hcharacter : 2 * (i - d) - 1 = 2 * i - 1 - 2 * d := by ring
  have hexponent : -2 * (i - d) = -2 * i + 2 * d := by ring
  simp only [shiftedTameGaussBlock, mul_zero, sub_zero, zero_sub, add_zero,
    hfirst, hsecond, hcharacter, hexponent]

set_option maxHeartbeats 800000 in
/-- Torsion translation adds no local squared norm loss on the same annulus. -/
theorem sum_normSq_shiftedTameGaussBlock_le (kappa : MulChar F Complex)
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) (m : Nat) [NeZero m]
    (z : Complex) (d : ZMod m) (hz : norm z <= 1)
    (hlower : 1 <= (Fintype.card F : Real) * Complex.normSq z)
    (hupper : norm z ^ m <= (Fintype.card F : Real) ^ (-1 : Int))
    (v : ZMod m -> Complex) :
    Finset.univ.sum (fun i => Complex.normSq (Finset.univ.sum (fun j =>
      shiftedTameGaussBlock kappa psi m z d i j * v j))) <=
      4 * Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  let p : Equiv.Perm (ZMod m) := Equiv.addRight (-1)
  let t : Equiv.Perm (ZMod m) := (Equiv.neg (ZMod m)).trans (Equiv.addRight (2 * d))
  have h := sum_normSq_twoPermutationGaussBlock_le
    (fun i : ZMod m => kappa ^ (2 * i - 1 - 2 * d).val) psi hpsi p t
    (fun i => (-2 * i + 2 * d).val) m z hz hlower hupper v
  simpa [p, t, shiftedTameGaussBlock, twoPermutationGaussBlock,
    sub_eq_add_neg, add_comm] using h

end MulChar
