/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRegularFactor

/-! # Exact floor and logarithmic degree budgets for one factor family -/

set_option autoImplicit false
set_option Elab.async false

theorem hamiltonian_exp_quarter_square (L : Real) (hL : 0 <= L) :
    L ^ 2 <= 4 * Real.exp L := by
  have h := Real.add_one_le_exp (L / 2)
  have hhalf : 0 <= L / 2 := div_nonneg hL (by norm_num)
  have hle : L / 2 <= Real.exp (L / 2) := by linarith only [h]
  have hmul := mul_le_mul hle hle hhalf (le_of_lt (Real.exp_pos (L / 2)))
  have heq : Real.exp (L / 2) ^ 2 = Real.exp L := by
    calc
      _ = Real.exp ((2 : Real) * (L / 2)) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (L / 2) 2).symm
      _ = Real.exp L := by congr 1; ring
  have hsq : (L / 2) ^ 2 <= Real.exp (L / 2) ^ 2 := by nlinarith only [hmul]
  rw [heq] at hsq
  nlinarith only [hsq]

theorem hamiltonian_logarithmic_degree_lower (n : Real) (hn : 1 < n) :
    Real.log n / 4 <= n / Real.log n := by
  have hL : 0 < Real.log n := Real.log_pos hn
  have hn0 : 0 < n := lt_trans (by norm_num) hn
  have hs := hamiltonian_exp_quarter_square (Real.log n) (le_of_lt hL)
  rw [Real.exp_log hn0] at hs
  have hc : (n / Real.log n) * Real.log n = n := by
    have h := (div_eq_iff (ne_of_gt hL)).mp
      (rfl : n / Real.log n = n / Real.log n)
    exact h.symm
  apply le_of_not_gt
  intro hbad
  have hm := mul_lt_mul_of_pos_right hbad hL
  nlinarith only [hs, hc, hm]

theorem hamiltonian_factor_reciprocal_degree
    (L D : Real) (hL : 0 < L) (hLower : L / 4 <= D) :
    1 / D <= 4 / L := by
  have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
    (div_pos hL (by norm_num)) hLower
  have heq : (1 : Real) / (L / 4) = 4 / L := by
    field_simp [ne_of_gt hL]
  exact hdiv.trans_eq heq

theorem hamiltonian_factor_floor_bounds (D eps : Real)
    (hD : 16 <= D) (heps : 0 <= eps) (hepsSmall : eps <= (1 / 100 : Real)) :
    let r := Nat.floor ((1 - 10 * eps) * D)
    And (1 <= r) (And ((r : Real) <= D)
      (And (D - (r : Real) <= 10 * eps * D + 1) (D / 2 <= (r : Real)))) := by
  let r := Nat.floor ((1 - 10 * eps) * D)
  have hD0 : 0 <= D := by linarith only [hD]
  have hepD := mul_le_mul_of_nonneg_right hepsSmall hD0
  have hx0 : 0 <= (1 - 10 * eps) * D := by nlinarith only [hepD, hD]
  have hf : (r : Real) <= (1 - 10 * eps) * D := Nat.floor_le hx0
  have hlow : (1 - 10 * eps) * D < (r : Real) + 1 :=
    Nat.lt_floor_add_one ((1 - 10 * eps) * D)
  have hepD0 : 0 <= eps * D := mul_nonneg heps hD0
  have hrOne : (1 : Real) <= (r : Real) := by nlinarith only [hlow, hepD, hD]
  have hrNat : 1 <= r := by exact_mod_cast hrOne
  refine And.intro hrNat (And.intro ?_ (And.intro ?_ ?_))
  . nlinarith only [hf, hepD0]
  . nlinarith only [hlow]
  . nlinarith only [hlow, hepD, hD]

theorem hamiltonian_factor_floor_relative
    (D eps : Real) (hD : 16 <= D)
    (heps : 0 <= eps) (hepsSmall : eps <= (1 / 100 : Real)) :
    let r := Nat.floor ((1 - 10 * eps) * D)
    abs ((r : Real) / D - 1) <= 10 * eps + 1 / D := by
  let r := Nat.floor ((1 - 10 * eps) * D)
  change abs ((r : Real) / D - 1) <= 10 * eps + 1 / D
  have h := hamiltonian_factor_floor_bounds D eps hD heps hepsSmall
  have hDpos : 0 < D := by linarith only [hD]
  have hratio : (r : Real) / D <= 1 := by
    have hd := div_le_div_of_nonneg_right h.2.1 (le_of_lt hDpos)
    simpa only [div_self (ne_of_gt hDpos)] using hd
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  have hdef := div_le_div_of_nonneg_right h.2.2.1 (le_of_lt hDpos)
  have hl : (D - (r : Real)) / D = 1 - (r : Real) / D := by
    rw [sub_div, div_self (ne_of_gt hDpos)]
  have hu : (10 * eps * D + 1) / D = 10 * eps + 1 / D := by
    field_simp [ne_of_gt hDpos]
    <;> ring
  rw [hl, hu] at hdef
  linarith only [hdef]
