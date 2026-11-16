/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianTotientDiffusion

/-! # The full squared-sublogarithmic budget for every coprime modulus

The same ratio n / phi(n) is used in the proved density estimate and
the actual Hamiltonian-count envelope. Every positive coefficient is
quantified, and one threshold covers all larger moduli.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_totient_ratio_ge_one (n : Nat) (hn : 0 < n) :
    1 <= (n : Real) / (n.totient : Real) := by
  have hPhi : 0 < (n.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hPhiNe : Not ((n.totient : Real) = 0) := ne_of_gt hPhi
  have hPhiLe : (n.totient : Real) <= (n : Real) := by exact_mod_cast Nat.totient_le n
  apply (mul_le_mul_iff_of_pos_right hPhi).mp
  have hCancel : ((n : Real) / (n.totient : Real)) * (n.totient : Real) = (n : Real) := by
    field_simp
  rw [hCancel, one_mul]
  exact hPhiLe

theorem hamiltonian_totient_squared_sublogarithmic (b : Real) (hb : 0 < b) :
    exists N0 : Nat, 3 <= N0 /\ forall n : Nat, N0 <= n ->
      ((n : Real) / (n.totient : Real)) ^ 2 <= b * Real.log (n : Real) := by
  choose C hC hDensity using hamiltonian_totient_diffusion_uniform
  let eta := b / (2 * C ^ 2)
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
  have hEta : 0 < eta := div_pos hb (mul_pos (by norm_num) hC2)
  let range := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := (1 : Real)) (2 : Real)
      (by norm_num)).bound hEta)
  let x1 := range.choose
  let X := max 0 x1
  let N0 := max 3 (Nat.ceil (Real.exp X))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn
  have hn3 : 3 <= n := (le_max_left _ _).trans hn
  have hnPos : 0 < n := by omega
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hn3R : (3 : Real) <= (n : Real) := by exact_mod_cast hn3
  have hnCeil : Nat.ceil (Real.exp X) <= n := (le_max_right _ _).trans hn
  have hExp : Real.exp X <= (n : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnCeil)
  let Y := Real.log (3 * (n : Real))
  have hThree : 0 < 3 * (n : Real) := mul_pos (by norm_num) hnR
  have hY : 1 < Y := (Real.lt_log_iff_exp_lt hThree).mpr
    (Real.exp_one_lt_three.trans_le (by linarith only [hn3R]))
  have hYX : X <= Y := by
    calc
      _ = Real.log (Real.exp X) := (Real.log_exp X).symm
      _ <= _ := Real.log_le_log (Real.exp_pos _) (by linarith only [hExp, hnR])
  have hYx1 : x1 <= Y := (le_max_right _ _).trans hYX
  have hRaw := range.choose_spec Y hYx1
  simp only [Real.norm_eq_abs] at hRaw
  have hPow : (Real.log Y) ^ (2 : Real) = Real.log Y ^ (2 : Nat) :=
    Real.rpow_natCast _ 2
  rw [hPow, Real.rpow_one,
    abs_of_nonneg (sq_nonneg (Real.log Y)),
    abs_of_nonneg (le_trans (by norm_num : (0 : Real) <= 1) hY.le)] at hRaw
  have hLogY : 0 <= Real.log Y := Real.log_nonneg hY.le
  have hA := hDensity n hn3
  change (n : Real) / (n.totient : Real) <= C * Real.log Y at hA
  have hA0 : 0 <= (n : Real) / (n.totient : Real) :=
    div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n.totient)
  have hSquare := mul_le_mul hA hA hA0 (mul_nonneg hC.le hLogY)
  have hSquareBound : ((n : Real) / (n.totient : Real)) ^ 2 <= C ^ 2 * Real.log Y ^ 2 := by
    nlinarith only [hSquare]
  have hScaled := mul_le_mul_of_nonneg_left hRaw hC2.le
  have hCNe : Not (C = 0) := ne_of_gt hC
  have hClear : C ^ 2 * eta = b / 2 := by dsimp only [eta]; field_simp
  have hBudget : C ^ 2 * Real.log Y ^ 2 <= (b / 2) * Y := by
    calc
      _ <= C ^ 2 * (eta * Y) := hScaled
      _ = _ := by rw [<- mul_assoc, hClear]
  have hLog3 : Real.log 3 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) hn3R
  have hSplit : Y = Real.log 3 + Real.log (n : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hnR)
  have hDouble : Y <= 2 * Real.log (n : Real) := by linarith only [hLog3, hSplit]
  calc
    _ <= C ^ 2 * Real.log Y ^ 2 := hSquareBound
    _ <= (b / 2) * Y := hBudget
    _ <= (b / 2) * (2 * Real.log (n : Real)) :=
      mul_le_mul_of_nonneg_left hDouble (by positivity)
    _ = _ := by ring

theorem hamiltonian_totient_sublogarithmic (b : Real) (hb : 0 < b) :
    exists N0 : Nat, 3 <= N0 /\ forall n : Nat, N0 <= n ->
      (n : Real) / (n.totient : Real) <= b * Real.log (n : Real) := by
  choose N0 hN0 hSquare using hamiltonian_totient_squared_sublogarithmic b hb
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have hnPos : 0 < n := by omega
  have hOne := hamiltonian_totient_ratio_ge_one n hnPos
  have hNonneg : 0 <= (n : Real) / (n.totient : Real) := le_trans (by norm_num) hOne
  have h := mul_le_mul_of_nonneg_left hOne hNonneg
  have hToSquare : (n : Real) / (n.totient : Real) <=
      ((n : Real) / (n.totient : Real)) ^ 2 := by nlinarith only [h]
  exact hToSquare.trans (hSquare n hn)

end PrimeFactorOscillations
