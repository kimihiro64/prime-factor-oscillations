/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTotientCutoff

/-! # Uniform totient diffusion at every modulus

The logarithmic cutoff gives an absolute constant independent of n.
The finite small-modulus range is covered without numerical sampling.
This is the density input to the full coprime-circle count.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_totient_tail_exponent (L Y : Real)
    (hL : L <= Y) (hY : 0 < Y) (hLogY : 1 <= Real.log Y) :
    2 * L / (Y * Real.log Y) <= 2 := by
  have hLogPos : 0 < Real.log Y := lt_of_lt_of_le (by norm_num) hLogY
  have hDenPos : 0 < Y * Real.log Y := mul_pos hY hLogPos
  have hDenNe : Not (Y * Real.log Y = 0) := ne_of_gt hDenPos
  have hCancel : (2 * L / (Y * Real.log Y)) * (Y * Real.log Y) = 2 * L := by
    field_simp
  apply (mul_le_mul_iff_of_pos_right hDenPos).mp
  rw [hCancel]
  have hScale := mul_le_mul_of_nonneg_left hLogY hY.le
  nlinarith only [hL, hScale]

theorem hamiltonian_totient_diffusion_eventual :
    exists C : Real, 0 < C /\ exists N0 : Nat, 3 <= N0 /\
      forall n : Nat, N0 <= n ->
        (n : Real) / (n.totient : Real) <= C * Real.log (Real.log (3 * (n : Real))) := by
  choose C hC X hX hBound using hamiltonian_mertens_product_reciprocal_bound
  let Y0 := max 4 (max X (Real.exp 1))
  let N0 := max 3 (Nat.ceil (Real.exp Y0))
  refine Exists.intro (C * Real.exp 2) (And.intro (mul_pos hC (Real.exp_pos _))
    (Exists.intro N0 (And.intro (le_max_left _ _) ?_)))
  intro n hn
  have hn3 : 3 <= n := (le_max_left _ _).trans hn
  have hnPos : 0 < n := by omega
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hnCeil : Nat.ceil (Real.exp Y0) <= n := (le_max_right _ _).trans hn
  have hExp : Real.exp Y0 <= (n : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnCeil)
  let Y := Real.log (3 * (n : Real))
  have hY0 : Y0 <= Y := by
    calc
      _ = Real.log (Real.exp Y0) := (Real.log_exp Y0).symm
      _ <= _ := Real.log_le_log (Real.exp_pos _) (by linarith only [hExp, hnR])
  have hY4 : 4 <= Y := (le_max_left _ _).trans hY0
  have hYX : X <= Y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hY0
  have hYE : Real.exp 1 <= Y :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hY0
  have hYPos : 0 < Y := lt_of_lt_of_le (by norm_num : (0 : Real) < 4) hY4
  have hLogY : 1 <= Real.log Y := by
    calc
      _ = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= _ := Real.log_le_log (Real.exp_pos _) hYE
  have hLogN : Real.log (n : Real) <= Y :=
    Real.log_le_log hnR (by linarith only [hnR])
  have hTail : Real.exp (2 * Real.log (n : Real) / (Y * Real.log Y)) <= Real.exp 2 :=
    Real.exp_le_exp.mpr (hamiltonian_totient_tail_exponent _ _ hLogN hYPos hLogY)
  have hM := hBound Y hYX
  calc
    _ <= (1 / hamiltonianMertensProduct Y) *
        Real.exp (2 * Real.log (n : Real) / (Y * Real.log Y)) :=
      hamiltonian_totient_finite_cutoff n hnPos Y hY4
    _ <= (C * Real.log Y) * Real.exp 2 :=
      mul_le_mul hM.2 hTail (Real.exp_pos _).le
        (mul_nonneg hC.le (le_trans (by norm_num) hLogY))
    _ = _ := by dsimp [Y]; ring

theorem hamiltonian_totient_diffusion_uniform :
    exists C : Real, 0 < C /\ forall n : Nat, 3 <= n ->
      (n : Real) / (n.totient : Real) <= C * Real.log (Real.log (3 * (n : Real))) := by
  choose C hC N0 hN0 hLarge using hamiltonian_totient_diffusion_eventual
  let b := Real.log (Real.log 3)
  have hLog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 3)).mpr Real.exp_one_lt_three
  have hb : 0 < b := Real.log_pos hLog3
  let D := max C ((N0 : Real) / b)
  refine Exists.intro D (And.intro (hC.trans_le (le_max_left _ _)) ?_)
  intro n hn
  have hnPos : 0 < n := by omega
  have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast (show 1 <= n by omega)
  have hLogN : Real.log 3 <= Real.log (3 * (n : Real)) :=
    Real.log_le_log (by norm_num : (0 : Real) < 3) (by linarith only [hn1])
  have hbN : b <= Real.log (Real.log (3 * (n : Real))) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hLog3.le) hLogN
  have hNonneg : 0 <= Real.log (Real.log (3 * (n : Real))) :=
    hb.le.trans hbN
  by_cases hBig : N0 <= n
  case pos =>
    exact (hLarge n hBig).trans
      (mul_le_mul_of_nonneg_right (le_max_left C ((N0 : Real) / b)) hNonneg)
  case neg =>
    have hPhi : (1 : Real) <= (n.totient : Real) := by
      exact_mod_cast Nat.totient_pos.mpr hnPos
    have hInv : 1 / (n.totient : Real) <= 1 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hPhi
      simpa only [div_one] using h
    have hRatio : (n : Real) / (n.totient : Real) <= (n : Real) := by
      simpa only [div_eq_mul_inv, one_mul, mul_one] using
        mul_le_mul_of_nonneg_left hInv (Nat.cast_nonneg n)
    have hnN0 : (n : Real) <= (N0 : Real) := by
      exact_mod_cast (show n <= N0 by omega)
    have hbNe : Not (b = 0) := ne_of_gt hb
    have hCancel : ((N0 : Real) / b) * b = (N0 : Real) := by field_simp
    have hScale := mul_le_mul_of_nonneg_left hbN
      (div_nonneg (Nat.cast_nonneg N0) hb.le)
    rw [hCancel] at hScale
    have hD := mul_le_mul_of_nonneg_right (le_max_right C ((N0 : Real) / b)) hNonneg
    exact hRatio.trans (hnN0.trans (hScale.trans hD))

end PrimeFactorOscillations
