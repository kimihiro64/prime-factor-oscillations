/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorAmplification

/-! # Signed cycle counting with a fixed exceptional Fourier space -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_spectral_kappa_two_fifths :
    hamiltonianSpectralKappa (2 / 5 : Real) < 21 / 10 := by
  have hQuadratic := Real.quadratic_le_exp_of_nonneg
    (x := (42 / 125 : Real)) (by norm_num)
  have hExp : (29 / 21 : Real) < Real.exp (42 / 125 : Real) := by
    nlinarith only [hQuadratic]
  have hLog := Real.log_lt_log (by norm_num : (0 : Real) < 29 / 21) hExp
  rw [Real.log_exp] at hLog
  have hCoordinate : hamiltonianAmplificationCoordinate ((2 / 5 : Real) ^ 2) =
      Real.log (29 / 21 : Real) := by
    unfold hamiltonianAmplificationCoordinate
    have h := Real.log_div
      (by norm_num : Not ((1 + (2 / 5 : Real) ^ 2) = 0))
      (by norm_num : Not ((1 - (2 / 5 : Real) ^ 2) = 0))
    rw [<- h]
    congr 1
    norm_num
  have hKappa : hamiltonianSpectralKappa (2 / 5 : Real) =
      (25 / 4 : Real) * Real.log (29 / 21 : Real) := by
    unfold hamiltonianSpectralKappa
    rw [if_neg (by norm_num : Not ((2 / 5 : Real) = 0)), hCoordinate]
    norm_num
    <;> ring
  rw [hKappa]
  nlinarith only [hLog]

def hamiltonianFiniteFactorCountCost (k : Nat) (rho L : Real) : Real :=
  hamiltonianFiniteFactorDeterminantCost k (25 / 21) L *
    hamiltonianFiniteFactorDeterminantCost k (1 / (1 - rho ^ 2)) L *
      Real.exp (hamiltonianSpectralKappa (2 / 5 : Real) *
        (2 * (k : Real) * rho * L ^ 2 + (k : Real) * L ^ 4))

theorem hamiltonian_finite_factor_count_cost_positive
    (k : Nat) (rho L : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    0 < hamiltonianFiniteFactorCountCost k rho L := by
  have hr2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
  have hAlpha : 0 < 1 / (1 - rho ^ 2) := one_div_pos.mpr (sub_pos.mpr hr2)
  dsimp [hamiltonianFiniteFactorCountCost, hamiltonianFiniteFactorDeterminantCost]
  positivity

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]
variable [Fintype Jota] [DecidableEq Jota]

theorem hamiltonian_finite_factor_two_fifths_amplification
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (rho L : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hL : 0 <= L)
    (hB : B = R + U * V) (hNormB : norm B <= rho)
    (hNormR : norm R <= (2 / 5 : Real)) (hU : norm U <= L) (hV : norm V <= L) :
    hamiltonianMatrixGramAmplification B <=
      hamiltonianFiniteFactorCountCost (Fintype.card Jota) rho L *
        Real.exp (hamiltonianSpectralKappa (2 / 5 : Real) *
          Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2))) := by
  have h := hamiltonian_finite_factor_amplification_energy_bound B R U V rho (2 / 5) L
    hRho0 hRho1 (by norm_num) (by norm_num) hL hB hNormB hNormR hU hV
  norm_num only [show (1 / (1 - (2 / 5 : Real) ^ 2)) = 25 / 21 by norm_num] at h
  exact h

theorem hamiltonian_finite_factor_count_amplification_power
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (rho L n : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hL : 0 <= L)
    (hB : B = R + U * V) (hNormB : norm B <= rho)
    (hNormR : norm R <= (2 / 5 : Real)) (hU : norm U <= L) (hV : norm V <= L)
    (hn : 1 <= n)
    (hEnergy : Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2)) <=
      (7 / 10 : Real) * Real.log n)
    (hCost : hamiltonianFiniteFactorCountCost (Fintype.card Jota) rho L <=
      n ^ (3 / 100 : Real)) :
    hamiltonianMatrixGramAmplification B <= n ^ (3 / 2 : Real) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hLog : 0 <= Real.log n := Real.log_nonneg hn
  have hK : 0 <= hamiltonianSpectralKappa (2 / 5 : Real) :=
    hamiltonian_spectral_kappa_nonnegative (2 / 5) (by norm_num) (by norm_num)
  have hScaled := mul_le_mul_of_nonneg_left hEnergy hK
  have hCap := mul_le_mul_of_nonneg_right
    (le_of_lt hamiltonian_spectral_kappa_two_fifths)
      (mul_nonneg (by norm_num : (0 : Real) <= 7 / 10) hLog)
  have hExp : Real.exp (hamiltonianSpectralKappa (2 / 5 : Real) *
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2))) <=
        n ^ (147 / 100 : Real) := by
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    nlinarith only [hScaled, hCap]
  calc
    _ <= hamiltonianFiniteFactorCountCost (Fintype.card Jota) rho L *
        Real.exp (hamiltonianSpectralKappa (2 / 5 : Real) *
          Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2))) :=
      hamiltonian_finite_factor_two_fifths_amplification B R U V rho L
        hRho0 hRho1 hL hB hNormB hNormR hU hV
    _ <= n ^ (3 / 100 : Real) * n ^ (147 / 100 : Real) :=
      mul_le_mul hCost hExp (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg (le_of_lt hn0) _)
    _ = _ := by rw [<- Real.rpow_add hn0]; norm_num

universe u

theorem stochastic_fixed_factor_cycle_power_uniform
    (k : Nat) (rho L : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hL : 0 <= L) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real)
          (R : Matrix J J Real) (U : Matrix J (Fin k) Real)
          (V : Matrix (Fin k) J Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= rho ->
          a - 1 <= (7 / 10 : Real) * Real.log (Fintype.card J : Real) ->
          centeredKernel T q = R + U * V -> norm R <= (2 / 5 : Real) ->
          norm U <= L -> norm V <= L ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            (Fintype.card J : Real) ^ (-1 / 3 : Real) := by
  have hDelta : 0 < 1 - rho := sub_pos.mpr hRho1
  have hDelta1 : 1 - rho <= 1 := by linarith only [hRho0]
  have hRange := stochastic_weighted_cycle_power_decay_uniform.{u}
    (1 - rho) 2 (3 / 2) (1 / 3) hDelta hDelta1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine hRange.elim ?_
  intro NC hNC
  let C := hamiltonianFiniteFactorCountCost k rho L
  have hC : 0 < C := hamiltonian_finite_factor_count_cost_positive k rho L hRho0 hRho1
  have hCRange := hamiltonian_log_power_dominated_uniform C hC 0
    (3 / 100) (by norm_num)
  refine hCRange.elim ?_
  intro NL hNL
  let N0 := max (max NC NL) (Nat.ceil (Real.exp 1))
  refine Exists.intro N0 (And.intro
    (le_trans hNC.1 (le_trans (le_max_left _ _) (le_max_left _ _))) ?_)
  intro J instF instD instN hn T q a R U V hq ha hRow hCol hNonneg hUpper
    hNorm hCap hFactor hR hU hV
  have hnNC : NC <= Fintype.card J :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnNL : NL <= Fintype.card J :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnCeil : Nat.ceil (Real.exp 1) <= Fintype.card J :=
    le_trans (le_max_right _ _) hn
  have hn256 : (256 : Real) <= Fintype.card J := by
    exact_mod_cast le_trans hNC.1 hnNC
  have hn1 : (1 : Real) <= Fintype.card J := by linarith only [hn256]
  have hn0 : 0 < (Fintype.card J : Real) := by linarith only [hn256]
  have hExp : Real.exp 1 <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLog : 1 <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hSplit : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hn0)
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : a <= 2 * Real.log (2 * (Fintype.card J : Real)) := by
    linarith only [hCap, hLog, hSplit, hLog2]
  have hEnergy := (stochastic_total_energy T q a hq hRow hNonneg hUpper).trans hCap
  have hCost : hamiltonianFiniteFactorCountCost (Fintype.card (Fin k)) rho L <=
      (Fintype.card J : Real) ^ (3 / 100 : Real) := by
    simpa only [Fintype.card_fin, pow_zero, mul_one] using hNL.2 (Fintype.card J) hnNL
  have hAmp := hamiltonian_finite_factor_count_amplification_power
    (centeredKernel T q) R U V rho L (Fintype.card J)
      hRho0 hRho1 hL hFactor hNorm hR hU hV hn1 hEnergy hCost
  have hNormDelta : norm (centeredKernel T q) <= 1 - (1 - rho) := by
    simpa only [sub_sub_cancel] using hNorm
  simpa only [neg_div] using
    hNC.2 J hnNC T q a hq ha hA hRow hCol hNonneg hUpper hNormDelta hAmp

end PrimeFactorOscillations
