/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.InverseDeletionWave

/-!
# MaskedSignedWave

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described by LICENSE.
Authors: Jonas
-/


noncomputable section
open scoped BigOperators Classical

namespace OAI.SevenEighths.MaskedSignedWave

open HeckeFamily HeckeDeletionBounds InverseDeletionWave

theorem squared_norm_relative_error (delta : Real) (hdelta : 0 <= delta)
    (x y : Complex) (hxy : norm (x - y) <= delta * norm y) :
    abs ((norm x) ^ 2 - (norm y) ^ 2) <= delta * (delta + 2) * (norm y) ^ 2 := by
  have hd := abs_norm_sub_norm_le x y
  have hx : norm x <= (delta + 1) * norm y := by
    have h := norm_add_le (x - y) y
    simp only [sub_add_cancel] at h
    nlinarith
  have hn := norm_nonneg x
  have hm := norm_nonneg y
  have he : (norm x) ^ 2 - (norm y) ^ 2 =
      (norm x - norm y) * (norm x + norm y) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg hn hm)]
  calc
    _ <= (delta * norm y) * ((delta + 2) * norm y) :=
      mul_le_mul (hd.trans hxy) (by linarith) (add_nonneg hn hm)
        (mul_nonneg hdelta hm)
    _ = _ := by ring

theorem signed_square_sum_error {I : Type*} (S : Finset I)
    (nu : I -> Real) (A B : I -> Complex) (delta : Real) (hdelta : 0 <= delta)
    (hnu : forall i, Membership.mem S i -> abs (nu i) <= 1)
    (herr : forall i, Membership.mem S i -> norm (A i - B i) <= delta * norm (B i)) :
    abs (S.sum (fun i => nu i * ((norm (A i)) ^ 2 - (norm (B i)) ^ 2))) <=
      delta * (delta + 2) * S.sum (fun i => (norm (B i)) ^ 2) := by
  calc
    _ = norm (S.sum (fun i => nu i * ((norm (A i)) ^ 2 - (norm (B i)) ^ 2))) :=
      (Real.norm_eq_abs _).symm
    _ <= S.sum (fun i => norm (nu i * ((norm (A i)) ^ 2 - (norm (B i)) ^ 2))) :=
      norm_sum_le _ _
    _ <= S.sum (fun i => delta * (delta + 2) * (norm (B i)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ <= 1 * abs ((norm (A i)) ^ 2 - (norm (B i)) ^ 2) :=
          mul_le_mul_of_nonneg_right (hnu i hi) (abs_nonneg _)
        _ <= _ := by
          simpa only [one_mul] using squared_norm_relative_error delta hdelta
            (A i) (B i) (herr i hi)
    _ = _ := by rw [Finset.mul_sum]

def windowError (sigma kappa D : Real) : Real :=
  Real.exp (localBound sigma * kappa / Real.log D) - 1

theorem windowError_nonneg {sigma kappa D : Real} (hsigma : 0 < sigma)
    (hkappa : 0 <= kappa) (hD : 1 < D) : 0 <= windowError sigma kappa D := by
  unfold windowError
  have h := Real.add_one_le_exp (localBound sigma * kappa / Real.log D)
  have hp : 0 <= localBound sigma * kappa / Real.log D :=
    div_nonneg (mul_nonneg (localBound_pos hsigma).le hkappa) (Real.log_pos hD).le
  linarith

theorem euler_signed_energy_log_window {I : Type*} (S : Finset I)
    (nu : I -> Real) (c : I -> Complex) (M : I -> Ideal O) (psi : I -> Character)
    (sigma kappa D : Real) (hsigma : 0 < sigma) (hkappa : 0 <= kappa) (hD : 1 < D)
    (hnu : forall i, Membership.mem S i -> abs (nu i) <= 1)
    (hmask : forall i, Membership.mem S i ->
      ((radical (M i)).absNorm : Real) <= D ^ kappa)
    {s rho : Complex} (hs : sigma <= s.re) (hrho : sigma <= rho.re)
    (hwindow : norm (rho - s) <= 1 / (Real.log D) ^ 2) :
    abs (S.sum (fun i => nu i *
      ((norm (c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) s))) ^ 2 -
       (norm (c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) rho))) ^ 2))) <=
      windowError sigma kappa D * (windowError sigma kappa D + 2) *
        S.sum (fun i =>
          (norm (c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) rho))) ^ 2) := by
  apply signed_square_sum_error S nu _ _ (windowError sigma kappa D)
    (windowError_nonneg hsigma hkappa hD) hnu
  intro i hi
  have hne := HeckeFiniteDeletion.factors_ne_zero (M i) (psi i) (hsigma.trans_le hrho)
  have he : c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) s) -
      c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) rho) =
      (c i * Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) rho)) *
        (Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) s) /
          Inv.inv (HeckeFiniteDeletion.factors (M i) (psi i) rho) - 1) := by
    field_simp
    <;> ring
  rw [he, norm_mul, mul_comm (windowError sigma kappa D)]
  exact mul_le_mul_of_nonneg_left
    (inverse_relative_log_window sigma hsigma D kappa hD hkappa
      (M i) (psi i) (hmask i hi) hs hrho hwindow) (norm_nonneg _)

end OAI.SevenEighths.MaskedSignedWave
