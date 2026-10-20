/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticCarrierPacket

/-!
# QuadraticSquareExtraction

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Positive square-row extraction from the full quadratic moment

All rows and both column sums are retained. Only the selected square
rows are used for the lower bound; their coprimality hypotheses ensure
that the target cofactor sum survives without a character mask.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticSquareExtraction

open QuadraticCarrierPacket

theorem square_injective : Function.Injective (fun r : Nat => r ^ 2) := by
  intro x y hxy
  have heq : (x : Real) ^ 2 = (y : Real) ^ 2 := by exact_mod_cast hxy
  have hx : (0 : Real) <= x := Nat.cast_nonneg x
  have hy : (0 : Real) <= y := Nat.cast_nonneg y
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  . have hd : (0 : Real) < (y : Real) - (x : Real) := by
      exact sub_pos.mpr (by exact_mod_cast hlt)
    have hs : (0 : Real) < (y : Real) + (x : Real) := by linarith
    have hp := mul_pos hd hs
    nlinarith
  . have hd : (0 : Real) < (x : Real) - (y : Real) := by
      exact sub_pos.mpr (by exact_mod_cast hgt)
    have hs : (0 : Real) < (x : Real) + (y : Real) := by linarith
    have hp := mul_pos hd hs
    nlinarith

theorem full_energy_ge_square_rows (rows bases s t : Finset Nat)
    (a v : Nat -> Complex) (w : Nat -> Real)
    (hw : forall u, Membership.mem rows u -> 0 <= w u)
    (hRows : forall r, Membership.mem bases r -> Membership.mem rows (r ^ 2))
    (hS : forall r, Membership.mem bases r ->
      forall n, Membership.mem s n -> (r : Int).gcd n = 1)
    (hT : forall r, Membership.mem bases r ->
      forall q, Membership.mem t q -> (r : Int).gcd q = 1) :
    (bases.sum fun r => w (r ^ 2)) *
        Complex.normSq (s.sum a) * Complex.normSq (t.sum v) <=
      GaussianTwoDiagonal.energy rows s t
        (fun n u => a n * kernel u n)
        (fun q u => v q * kernel u q) w := by
  classical
  let e : Nat -> Real := fun u =>
    w u * Complex.normSq (s.sum fun n => a n * kernel u n) *
      Complex.normSq (t.sum fun q => v q * kernel u q)
  have hSubset : bases.image (fun r => r ^ 2) <= rows := by
    intro u hu
    cases Finset.mem_image.mp hu with
    | intro r hr =>
      rw [<- hr.2]
      exact hRows r hr.1
  have hNonneg : forall u, Membership.mem rows u -> 0 <= e u := by
    intro u hu
    exact mul_nonneg (mul_nonneg (hw u hu) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)
  have hLE := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun u hu _ => hNonneg u hu)
  rw [Finset.sum_image (fun x _ y _ h => square_injective h)] at hLE
  calc
    _ = bases.sum (fun r => e (r ^ 2)) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only [e]
      rw [square_row_amplitude s a r (hS r hr),
        square_row_amplitude t v r (hT r hr)]
    _ <= rows.sum e := hLE
    _ = _ := rfl

end PrimeFactorOscillations.QuadraticSquareExtraction

