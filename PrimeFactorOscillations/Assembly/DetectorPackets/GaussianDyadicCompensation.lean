/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Basic
import PrimeFactorOscillations.Proof.DetectorPackets.GaussianLatticeCount

/-!
# GaussianDyadicCompensation

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
# Uniform dyadic Gaussian compensation weights

The quartic polynomial compensator has weight 1 / N(p) and dilation N(p)^4.
For each complementary tuple its moving coprimality mask is a row restriction.
The harmonic mass below is uniform in the growing Gaussian dyad. This is a
normalization input to the BGL low packet, not the large sieve or zero exclusion.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianDyadicCompensation

abbrev G := Zsqrtd (-1)

theorem dyadic_card (H : Nat) (hH : 1 <= H) (S : Finset G)
    (hupper : forall z, Membership.mem S z ->
      z.norm <= ((2*H : Nat) : Int)) :
    S.card <= 18*H := by
  have hcut : 1 <= 2*H := by omega
  have hh := GaussianLatticeCount.finite_set_card_le S (2*H) hcut hupper
  omega

theorem harmonic_bound (H : Nat) (hH : 1 <= H) (S : Finset G)
    (hlower : forall z, Membership.mem S z -> (H : Int) <= z.norm)
    (hupper : forall z, Membership.mem S z ->
      z.norm <= ((2*H : Nat) : Int)) :
    S.sum (fun z => 1/(z.norm : Real)) <= 18 := by
  have hpos : (0 : Real) < (H : Real) := by
    have hnat : 0 < H := by omega
    exact_mod_cast hnat
  have hcard : (S.card : Real) <= 18*(H : Real) := by
    exact_mod_cast dyadic_card H hH S hupper
  calc
    _ <= S.sum (fun _ => 1/(H : Real)) := by
      apply Finset.sum_le_sum
      intro z hz
      have hzreal : (H : Real) <= (z.norm : Real) := by
        exact_mod_cast hlower z hz
      exact one_div_le_one_div_of_le hpos hzreal
    _ = (S.card : Real)/(H : Real) := by simp [div_eq_mul_inv]
    _ <= 18 := by
      have hh := div_le_div_of_nonneg_right hcard hpos.le
      simpa only [mul_div_assoc, div_self hpos.ne', mul_one] using hh

theorem weighted_harmonic_bound (H : Nat) (hH : 1 <= H) (S : Finset G)
    (hlower : forall z, Membership.mem S z -> (H : Int) <= z.norm)
    (hupper : forall z, Membership.mem S z ->
      z.norm <= ((2*H : Nat) : Int))
    (w : G -> Complex) (B : Real) (hB : 0 <= B)
    (hw : forall z, Membership.mem S z -> norm (w z) <= B) :
    S.sum (fun z => norm (w z)*(1/(z.norm : Real))) <= 18*B := by
  have hpos : (0 : Real) < (H : Real) := by
    have hnat : 0 < H := by omega
    exact_mod_cast hnat
  calc
    _ <= S.sum (fun z => B*(1/(z.norm : Real))) := by
      apply Finset.sum_le_sum
      intro z hz
      have hzreal : (H : Real) <= (z.norm : Real) := by
        exact_mod_cast hlower z hz
      exact mul_le_mul_of_nonneg_right (hw z hz)
        (one_div_nonneg.mpr (hpos.le.trans hzreal))
    _ = B*S.sum (fun z => 1/(z.norm : Real)) := (Finset.mul_sum _ _ _).symm
    _ <= B*18 := mul_le_mul_of_nonneg_left
      (harmonic_bound H hH S hlower hupper) hB
    _ = 18*B := by ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Complex E]

theorem packet_bound (H : Nat) (hH : 1 <= H) (S : Finset G)
    (hlower : forall z, Membership.mem S z -> (H : Int) <= z.norm)
    (hupper : forall z, Membership.mem S z ->
      z.norm <= ((2*H : Nat) : Int))
    (w : G -> Complex) (B : Real) (hB : 0 <= B)
    (hw : forall z, Membership.mem S z -> norm (w z) <= B)
    (v : G -> E) (L : Real) (hL : 0 <= L)
    (hv : forall z, Membership.mem S z -> norm (v z) <= L) :
    norm (S.sum (fun z => HSMul.hSMul
      (w z*Complex.ofReal (1/(z.norm : Real))) (v z))) <= 18*B*L := by
  have hpos : (0 : Real) < (H : Real) := by
    have hnat : 0 < H := by omega
    exact_mod_cast hnat
  calc
    _ <= S.sum (fun z => norm (HSMul.hSMul
        (w z*Complex.ofReal (1/(z.norm : Real))) (v z))) := norm_sum_le _ _
    _ <= S.sum (fun z => (norm (w z)*(1/(z.norm : Real)))*L) := by
      apply Finset.sum_le_sum
      intro z hz
      have hzreal : (H : Real) <= (z.norm : Real) := by
        exact_mod_cast hlower z hz
      have hinv : 0 <= 1/(z.norm : Real) :=
        one_div_nonneg.mpr (hpos.le.trans hzreal)
      rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hinv]
      exact mul_le_mul_of_nonneg_left (hv z hz)
        (mul_nonneg (norm_nonneg _) hinv)
    _ = S.sum (fun z => norm (w z)*(1/(z.norm : Real)))*L :=
      (Finset.sum_mul _ _ _).symm
    _ <= (18*B)*L := mul_le_mul_of_nonneg_right
      (weighted_harmonic_bound H hH S hlower hupper w B hB hw) hL
    _ = 18*B*L := rfl

end PrimeFactorOscillations.GaussianDyadicCompensation

