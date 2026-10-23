/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelAllCarrierReadout
import PrimeFactorOscillations.Helpers.PrimePowerReturnAllPrimes

/-!
# The actual unit-to-residue bridge for every positive modulus

Finite bijections identify the full native unit and power-kernel sums with
the existing intrinsic rational coefficient observable. No squarefreeness
or local-period qualification is assumed in this bridge.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open CarmichaelCarrierReadout ModularReturnFourier

theorem native_unit_sum_indicator (n : Nat) [NeZero n] (f : ZMod n -> Complex) :
    Finset.univ.sum (fun u : Units (ZMod n) => f (u : ZMod n)) =
      Finset.univ.sum (fun x : ZMod n => if IsUnit x then f x else 0) := by
  classical
  rw [<- Finset.sum_filter]
  apply Finset.sum_bij (fun (u : Units (ZMod n)) _ => (u : ZMod n))
  { intro u _
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) u.isUnit) }
  { intro u _ v _ huv
    exact Units.ext huv }
  { intro x hx
    have hu := (Finset.mem_filter.mp hx).2
    exact Exists.intro hu.unit (Exists.intro (Finset.mem_univ _) hu.unit_spec) }
  { intro u _
    rfl }

theorem native_return_sum_indicator (n : Nat) [NeZero n] (k : Nat)
    (f : ZMod n -> Complex) :
    Finset.univ.sum (fun u : powerKernel n k => f (u.val : ZMod n)) =
      Finset.univ.sum (fun x : ZMod n =>
        if And (IsUnit x) (x ^ k = 1) then f x else 0) := by
  classical
  rw [<- Finset.sum_filter]
  apply Finset.sum_bij (fun (u : powerKernel n k) _ => (u.val : ZMod n))
  { intro u _
    have hk : u.val ^ k = 1 := u.property
    have hc := congrArg (fun v : Units (ZMod n) => (v : ZMod n)) hk
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hc
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_univ _) (And.intro u.val.isUnit hc)) }
  { intro u _ v _ huv
    apply Subtype.ext
    exact Units.ext huv }
  { intro x hx
    have data := (Finset.mem_filter.mp hx).2
    let u : Units (ZMod n) := data.1.unit
    have hk : u ^ k = 1 := by
      apply Units.ext
      change (u : ZMod n) ^ k = 1
      rw [show (u : ZMod n) = x from data.1.unit_spec]
      exact data.2
    let r : powerKernel n k := Subtype.mk u hk
    refine Exists.intro r (Exists.intro (Finset.mem_univ _) ?_)
    change (u : ZMod n) = x
    exact data.1.unit_spec }
  { intro u _
    rfl }

theorem unit_count_eq_native (n : Nat) [NeZero n] :
    (unitCount n : Complex) = (Fintype.card (Units (ZMod n)) : Complex) := by
  classical
  rw [unitCount, Rat.cast_sum]
  calc
    _ = Finset.univ.sum (fun x : ZMod n => if IsUnit x then (1 : Complex) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : IsUnit x <;> simp [unitCoefficient, hx]
    _ = Finset.univ.sum (fun _ : Units (ZMod n) => (1 : Complex)) :=
      (native_unit_sum_indicator n (fun _ => (1 : Complex))).symm
    _ = _ := by simp

theorem power_count_eq_native (n : Nat) [NeZero n] (k : Nat) :
    (powerCount n k : Complex) = (Fintype.card (powerKernel n k) : Complex) := by
  classical
  rw [powerCount, Rat.cast_sum]
  calc
    _ = Finset.univ.sum (fun x : ZMod n =>
        if And (IsUnit x) (x ^ k = 1) then (1 : Complex) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hu : IsUnit x <;> by_cases hx : x ^ k = 1 <;>
        simp [powerCoefficient, hu, hx]
    _ = Finset.univ.sum (fun _ : powerKernel n k => (1 : Complex)) :=
      (native_return_sum_indicator n k (fun _ => (1 : Complex))).symm
    _ = _ := by simp

theorem native_return_fourier (n : Nat) [NeZero n] (k h : Nat) :
    returnTransform n k h = residueFourier n (powerCoefficient n k) h := by
  classical
  rw [returnTransform, native_return_sum_indicator n k
    (fun x => ZMod.stdAddChar ((h : ZMod n) * x))]
  unfold residueFourier
  apply Finset.sum_congr rfl
  intro x _
  by_cases hu : IsUnit x <;> by_cases hx : x ^ k = 1 <;>
    simp [powerCoefficient, hu, hx]

theorem native_unit_fourier (n : Nat) [NeZero n] (h : Nat) :
    LPF.lpfRamanujanSum (q := n) h = residueFourier n (unitCoefficient n) h := by
  classical
  rw [LPF.lpfRamanujanSum, native_unit_sum_indicator n
    (fun x => ZMod.stdAddChar (x * (h : ZMod n)))]
  unfold residueFourier
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x <;> simp [unitCoefficient, hx, mul_comm]

theorem intrinsic_eq_native (n : Nat) [NeZero n] (k h : Nat) :
    residueFourier n (centeredPower n k) h = centeredTransform n k h := by
  change residueFourier n (fun x =>
    unitCount n * powerCoefficient n k x - powerCount n k * unitCoefficient n x) h = _
  rw [CarmichaelAllCarrierReadout.fourier_sub, fourier_const_mul, fourier_const_mul,
    unit_count_eq_native, power_count_eq_native, <- native_return_fourier,
    <- native_unit_fourier]
  rfl

end PrimeFactorOscillations.PrimePowerReturnSpectrum
