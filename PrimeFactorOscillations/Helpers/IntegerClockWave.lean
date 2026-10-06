/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasSpatialClock

/-!
# RH waves at fine-tracked integer clocks

Transfers the full spatial wave to a reference clock while retaining
the zero wave at the exact integer prefix endpoint.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open Robin1984

/-- Transport the existing full RH wave to a fine-tracked integer clock.
The zero wave is kept at the exact prefix endpoint P-1. -/
theorem tendsto_integer_clock_reference_wave (P : Nat -> Nat) (T : Nat -> Real)
    (hP : Tendsto (fun k : Nat => (P k : Real)) atTop atTop)
    (hTrack : Tendsto (fun k : Nat =>
      (T k - nicolasPrimeProductClock (P k - 1 : Nat)) / Real.sqrt (P k)) atTop (nhds 0))
    (hRH : RiemannHypothesis) :
    Tendsto (fun k : Nat =>
      (T k - Chebyshev.theta (P k - 1 : Nat)) / Real.sqrt (P k) -
        (2 + nicolasZeroWave (P k - 1 : Nat))) atTop (nhds 0) := by
  let X : Nat -> Real := fun k => (P k - 1 : Nat)
  have hX : Tendsto X atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hP.eventually (eventually_ge_atTop (max 1 (b + 1)))] with k hk
    have hp1 : 1 <= P k := by exact_mod_cast (le_max_left _ _).trans hk
    have hb := (le_max_right _ _).trans hk
    dsimp [X]
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith
  have hInner : Tendsto (fun k : Nat => X k / (P k : Real)) atTop (nhds 1) := by
    have hInv : Tendsto (fun k : Nat => (1 : Real) / (P k : Real)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hP
    have h := hInv.const_sub 1
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [hP.eventually (eventually_ge_atTop (2 : Real))] with k hk
    have hp1 : 1 <= P k := by exact_mod_cast (show (1 : Real) <= P k by linarith)
    have hp0 : Not ((P k : Real) = 0) := by linarith
    dsimp [X]
    rw [Nat.cast_sub hp1, Nat.cast_one]
    field_simp
  let q : Nat -> Real := fun k => Real.sqrt (X k) / Real.sqrt (P k)
  have hq : Tendsto q atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hInner
    simp only [Real.sqrt_one, Function.comp_def] at h
    apply h.congr'
    filter_upwards [] with k
    exact Real.sqrt_div (show 0 <= X k by dsimp [X]; positivity) (P k)
  have hBase : Tendsto (fun k : Nat =>
      (nicolasPrimeProductClock (X k) - Chebyshev.theta (X k)) / Real.sqrt (X k) -
        (2 + nicolasZeroWave (X k))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_nicolasPrimeProductClock_normalized_error hRH).comp hX
  let B : Real := 2 + abs (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))
  have hWaveBound : Filter.Eventually (fun k : Nat =>
      abs (2 + nicolasZeroWave (X k)) <= B) atTop := by
    filter_upwards [hX.eventually (eventually_ge_atTop (2 : Real))] with k hk
    have hW := abs_nicolasZeroWave_le hRH (by linarith : 1 < X k)
    have hTri := abs_add_le (2 : Real) (nicolasZeroWave (X k))
    norm_num at hTri
    dsimp [B]
    linarith [le_abs_self (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))]
  have hWaveSmall : Tendsto (fun k : Nat =>
      (2 + nicolasZeroWave (X k)) * (q k - 1)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hBound : Tendsto (fun k : Nat => B * abs (q k - 1)) atTop (nhds 0) := by
      simpa only [sub_self, Real.norm_eq_abs, norm_zero, mul_zero] using
        ((hq.sub_const 1).norm).const_mul B
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hBound
    filter_upwards [hWaveBound] with k hk
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have hProd := hBase.mul hq
  simp only [zero_mul] at hProd
  have hFinal := hTrack.add (hProd.add hWaveSmall)
  simp only [add_zero] at hFinal
  apply hFinal.congr'
  filter_upwards [hX.eventually (eventually_ge_atTop (2 : Real)),
    hP.eventually (eventually_ge_atTop (2 : Real))] with k hx hp
  have hx0 : Not (Real.sqrt (X k) = 0) := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hp0 : Not (Real.sqrt (P k) = 0) := (Real.sqrt_pos.mpr (by linarith)).ne'
  dsimp [q, X] at *
  field_simp
  <;> ring

end PrimeFactorOscillations
