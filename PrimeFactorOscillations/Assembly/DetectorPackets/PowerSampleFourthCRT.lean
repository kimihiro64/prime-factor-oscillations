/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.CompletedCRTPhase
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSamplePhysicalCRT

/-!
# PowerSampleFourthCRT

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.ProbePowerGauss
open scoped Classical BigOperators
open ActualEisensteinCubic ActualEisensteinCoordinates ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein ProbePhysical ProbePhase
local notation "O" => ActualEisensteinCubic.O

def powerCRTMultiplier (d : Nat) (A B s r : O) : Complex :=
  sexticPair s r *
    (idealRowHom ((B * r) ^ d) (Ideal.span {A}) /
      idealRowHom ((B * r) ^ d) (Ideal.span {s})) *
    (idealRowHom ((A * s) ^ d) (Ideal.span {B}) /
      idealRowHom ((A * s) ^ d) (Ideal.span {r}))

theorem fourthCRTMultiplier_eq (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : Dvd.dvd (goodLambda ^ 2) (A - 1))
    (hpB : Dvd.dvd (goodLambda ^ 2) (B - 1))
    (hps : Dvd.dvd (goodLambda ^ 2) (s - 1))
    (hpr : Dvd.dvd (goodLambda ^ 2) (r - 1))
    (hcop : IsCoprime (A * s) (B * r)) :
    powerCRTMultiplier 4 A B s r =
      sexticPair A B ^ 4 * reciprocitySign s r := by
  let R := sexticPair s r
  let P := sexticPair A B
  let S := reciprocitySign A r * reciprocitySign B s
  let T :=
    (idealRowHom (B * r) (Ideal.span {A}) /
      idealRowHom (B * r) (Ideal.span {s})) *
    (idealRowHom (A * s) (Ideal.span {B}) /
      idealRowHom (A * s) (Ideal.span {r}))
  have hBs := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hAr := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  have hsr := hcop.of_mul_left_right.of_mul_right_right
  have hsr0 := idealRowHom_ne_zero_of_coprime s r hs hsr
  have hrs0 := idealRowHom_ne_zero_of_coprime r s hr hsr.symm
  have hrecAr : idealRowHom r (Ideal.span {A}) =
      reciprocitySign A r * idealRowHom A (Ideal.span {r}) :=
    idealRowHom_primary_reciprocity A r hpA hpr hA hr
  have hrecBs : idealRowHom s (Ideal.span {B}) =
      reciprocitySign B s * idealRowHom B (Ideal.span {s}) :=
    idealRowHom_primary_reciprocity B s hpB hps hB hs
  have hT : R * T = P * S := by
    dsimp only [R, T, P, S, sexticPair]
    simp only [idealRowHom_argument_mul]
    rw [hrecAr, hrecBs]
    field_simp [hBs, hAr, hsr0, hrs0]
    <;> ring
  have hR3 : R ^ 3 = reciprocitySign s r :=
    sexticPair_cube_supported s r hs hr hps hpr hsr
  have hsign := reciprocitySign_sq s r
    (supported_residue_odd s hs) (supported_residue_odd r hr)
  have hR6 : R ^ 6 = 1 := by
    calc
      _ = (R ^ 3) ^ 2 := by ring
      _ = _ := by rw [hR3, hsign]
  have hS2 : S ^ 2 = 1 := by
    dsimp only [S]
    rw [mul_pow,
      reciprocitySign_sq A r (supported_residue_odd A hA) (supported_residue_odd r hr),
      reciprocitySign_sq B s (supported_residue_odd B hB) (supported_residue_odd s hs),
      mul_one]
  have hS4 : S ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, hS2, one_pow]
  have hphase : powerCRTMultiplier 4 A B s r = R * T ^ 4 := by
    unfold powerCRTMultiplier
    rw [idealRowHom_argument_pow _ _ _ hA, idealRowHom_argument_pow _ _ _ hs,
      idealRowHom_argument_pow _ _ _ hB, idealRowHom_argument_pow _ _ _ hr]
    dsimp only [R, T]
    simp only [mul_pow, div_pow]
    ring
  rw [hphase]
  calc
    _ = R * T ^ 4 * R ^ 6 := by rw [hR6, mul_one]
    _ = (R * T) ^ 4 * R ^ 3 := by ring
    _ = (P * S) ^ 4 * R ^ 3 := by rw [hT]
    _ = _ := by rw [mul_pow, hS4, hR3, mul_one]

theorem powerPhysicalFourier_fourth_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : Dvd.dvd (goodLambda ^ 2) (A - 1))
    (hpB : Dvd.dvd (goodLambda ^ 2) (B - 1))
    (hps : Dvd.dvd (goodLambda ^ 2) (s - 1))
    (hpr : Dvd.dvd (goodLambda ^ 2) (r - 1))
    (hcop : IsCoprime (A * s) (B * r)) (H : O) :
    powerPhysicalFourier 4 (A * B) (s * r)
      (mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB))
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
      (sexticPair A B ^ 4 * reciprocitySign s r) *
        powerPhysicalFourier 4 A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H *
        powerPhysicalFourier 4 B r (supportedElement_ne_zero B hB)
          (supportedElement_ne_zero r hr) H := by
  have he := powerPhysicalFourier_product 4 A B s r
    (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB) hs hr hcop H
  have hphase := fourthCRTMultiplier_eq A B s r hA hB hs hr hpA hpB hps hpr hcop
  calc
    _ = powerCRTMultiplier 4 A B s r *
        powerPhysicalFourier 4 A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H *
        powerPhysicalFourier 4 B r (supportedElement_ne_zero B hB)
          (supportedElement_ne_zero r hr) H := by
      simpa only [powerCRTMultiplier, sexticPair, div_eq_mul_inv, zpow_neg_one,
        mul_assoc] using he
    _ = _ := by rw [hphase]

def completedFourthFourier (A s : O) (hA : Not (A = 0))
    (hs : Not (s = 0)) (H : O) : Complex :=
  G s * powerPhysicalFourier 4 A s hA hs H

theorem completedFourthFourier_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : Dvd.dvd (goodLambda ^ 2) (A - 1))
    (hpB : Dvd.dvd (goodLambda ^ 2) (B - 1))
    (hps : Dvd.dvd (goodLambda ^ 2) (s - 1))
    (hpr : Dvd.dvd (goodLambda ^ 2) (r - 1))
    (hcop : IsCoprime (A * s) (B * r)) (H : O) :
    completedFourthFourier (A * B) (s * r)
      (mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB))
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
      sexticPair A B ^ 4 *
        completedFourthFourier A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H *
        completedFourthFourier B r (supportedElement_ne_zero B hB)
          (supportedElement_ne_zero r hr) H := by
  unfold completedFourthFourier
  rw [powerPhysicalFourier_fourth_product A B s r hA hB hs hr hpA hpB hps hpr hcop H,
    G_mul s r (supported_residue_odd s hs) (supported_residue_odd r hr)]
  have hsign := reciprocitySign_sq s r
    (supported_residue_odd s hs) (supported_residue_odd r hr)
  calc
    _ = (sexticPair A B ^ 4 *
        (G s * powerPhysicalFourier 4 A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H) *
        (G r * powerPhysicalFourier 4 B r (supportedElement_ne_zero B hB)
          (supportedElement_ne_zero r hr) H)) * reciprocitySign s r ^ 2 := by ring
    _ = _ := by rw [hsign, mul_one]

end OAI.SevenEighths.ProbePowerGauss
