/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCircleEntropyCount

/-! # Quantitative Stirling normalization with the full relative error -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_stirling_reciprocal_step (x : Real) (hx : 0 < x) :
    1 / (12 * x * (x + 1)) = 1 / (12 * x) - 1 / (12 * (x + 1)) := by
  field_simp [ne_of_gt hx, ne_of_gt (by linarith only [hx] : 0 < x + 1)]
  ring

theorem hamiltonian_stirling_log_tail (n : Nat) (hn : 1 <= n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) <=
      1 / (12 * (n : Real)) := by
  have hTel : forall k : Nat,
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k)) <=
        1 / (12 * (n : Real)) - 1 / (12 * (n + k : Nat)) := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero, sub_self, le_refl]
    | succ k ih =>
        have hmPos : (0 : Real) < (n + k : Nat) := Nat.cast_pos.mpr (by omega)
        have hStep := Stirling.log_stirlingSeq_sdiff_le (n + k)
        rw [hamiltonian_stirling_reciprocal_step _ hmPos] at hStep
        simp only [Nat.add_succ, Nat.cast_succ]
        linarith only [ih, hStep]
  have hBound (k : Nat) :
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k)) <=
        1 / (12 * (n : Real)) :=
    (hTel k).trans (sub_le_self _ (by positivity))
  have hSeq : Filter.Tendsto (fun k : Nat => Stirling.stirlingSeq (n + k))
      Filter.atTop (nhds (Real.sqrt Real.pi)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      Stirling.tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat n)
  have hPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hLog := (Real.continuousAt_log (ne_of_gt hPi)).tendsto.comp hSeq
  exact le_of_tendsto (tendsto_const_nhds.sub hLog) (Filter.Eventually.of_forall hBound)

theorem hamiltonian_exp_small_linear (x : Real) (hx : 0 <= x) (hSmall : x <= 1 / 2) :
    Real.exp x <= 1 + 2 * x := by
  have hGap : 0 < 1 - x := by linarith only [hSmall]
  have hExp := Real.exp_bound_div_one_sub_of_interval hx (by linarith only [hSmall])
  have hDen : (1 / 2 : Real) <= 1 - x := by linarith only [hSmall]
  have hDiv : x / (1 - x) <= x / (1 / 2) :=
    div_le_div_of_nonneg_left hx (by norm_num : (0 : Real) < 1 / 2) hDen
  calc
    _ <= 1 / (1 - x) := hExp
    _ = 1 + x / (1 - x) := by field_simp [ne_of_gt hGap]; ring
    _ <= 1 + x / (1 / 2) := by
      simpa only [add_comm] using _root_.add_le_add_left hDiv 1
    _ = _ := by ring

theorem hamiltonian_stirling_square_relative (n : Nat) (hn : 1 <= n) :
    abs (Stirling.stirlingSeq n ^ 2 / Real.pi - 1) <= 1 / (3 * (n : Real)) := by
  have hn0 : Not (n = 0) := by omega
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hSeq : 0 < Stirling.stirlingSeq n :=
    hPi.trans_le (Stirling.sqrt_pi_le_stirlingSeq hn0)
  have hLower : 0 <= Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
    exact sub_nonneg.mpr (Real.log_le_log hPi (Stirling.sqrt_pi_le_stirlingSeq hn0))
  let x := 2 * (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))
  have hx : 0 <= x := mul_nonneg (by norm_num) hLower
  have hUpper : x <= 1 / (6 * (n : Real)) := by
    have h := hamiltonian_stirling_log_tail n hn
    calc
      x <= 2 * (1 / (12 * (n : Real))) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hSmall : x <= 1 / 2 := by
    have hn1 : (1 : Real) <= n := by exact_mod_cast hn
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (by norm_num : (0 : Real) < 6) (by linarith only [hn1] : (6 : Real) <= 6 * (n : Real))
    exact hUpper.trans (h.trans (by norm_num))
  have hId : Real.exp x = Stirling.stirlingSeq n ^ 2 / Real.pi := by
    dsimp only [x]
    rw [show 2 * (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)) =
      (Real.log (Stirling.stirlingSeq n) + Real.log (Stirling.stirlingSeq n)) -
        (Real.log (Real.sqrt Real.pi) + Real.log (Real.sqrt Real.pi)) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hSeq, Real.exp_log hPi,
      Real.mul_self_sqrt Real.pi_pos.le]
    ring
  have hExpLower : 1 <= Real.exp x := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hx
  rw [<- hId, abs_of_nonneg (sub_nonneg.mpr hExpLower)]
  have hExpUpper := hamiltonian_exp_small_linear x hx hSmall
  have hDouble : 2 * (1 / (6 * (n : Real))) = 1 / (3 * (n : Real)) := by ring
  linarith only [hExpUpper, hUpper, hDouble]

end PrimeFactorOscillations
