/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicCount

/-! # The full squared-sublogarithmic aperiodic family asymptotic

The same arbitrary varying stochastic family is used in the finite
error bound and the positive-epsilon limit. No fixed-entry support,
fixed rank cutoff or lower positive-entry bound is imposed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

structure HamiltonianAperiodicStochasticFamily
    (delta : Real) (A : Nat -> Real)
    (T : (n : Nat) -> Matrix (Fin n) (Fin n) Real) : Prop where
  eventual_admissible : exists N0 : Nat, forall n : Nat, N0 <= n ->
    1 <= A n /\
      (forall i, Finset.univ.sum (fun j => T n i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => T n i j) = 1) /\
      (forall i j, 0 <= T n i j) /\
      (forall i j, T n i j <= A n * (1 / (n : Real))) /\
      norm (centeredKernel (T n) (1 / (n : Real))) <= 1 - delta
  squared_sublogarithmic : forall b : Real, 0 < b -> exists N0 : Nat,
    forall n : Nat, N0 <= n -> (A n) ^ 2 <= b * Real.log (n : Real)

theorem stochastic_aperiodic_family_quantitative
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (A : Nat -> Real) (T : (n : Nat) -> Matrix (Fin n) (Fin n) Real)
    (hFamily : HamiltonianAperiodicStochasticFamily delta A T) :
    exists N0 : Nat, 256 <= N0 /\ forall n : Nat, N0 <= n ->
      0 < hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) /\
        abs (hamiltonianCycleSum (T n) /
          hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) - 1) <=
            17 * (n : Real) ^ (-1 / 9 : Real) *
              Real.exp (hamiltonianAperiodicErrorConstant delta * (A n) ^ 2) /\
        abs (hamiltonianCycleSum (T n) /
          hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) - 1) <=
            17 * (n : Real) ^ (-1 / 18 : Real) := by
  choose P hP hUniform using stochastic_aperiodic_count_polylog_uniform delta hDelta hDelta1
  choose D hData using hFamily.eventual_admissible
  have hBudget := hamiltonian_aperiodic_density_budget delta hDelta
  choose B hSmall using hFamily.squared_sublogarithmic
    (hamiltonianAperiodicSublogDensity delta) hBudget.2.1
  let N0 := max P (max D B)
  refine Exists.intro N0 (And.intro (hP.trans (le_max_left _ _)) ?_)
  intro n hn
  have hnP : P <= n := (le_max_left _ _).trans hn
  have hnD : D <= n := by dsimp only [N0] at hn; omega
  have hnB : B <= n := by dsimp only [N0] at hn; omega
  have hn256 : 256 <= n := hP.trans hnP
  have hn1 : 1 <= n := by omega
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn1
  have hLog : 0 <= Real.log (n : Real) := Real.log_nonneg hnReal
  letI : NeZero n := NeZero.mk (by omega)
  have hq : (n : Real) * (1 / (n : Real)) = 1 := by field_simp
  have h := hData n hnD
  have ha0 : 0 <= A n := by linarith only [h.1]
  have haSquare : A n <= (A n) ^ 2 := by
    have hMul := mul_le_mul_of_nonneg_right h.1 ha0
    nlinarith only [hMul]
  have hCap : A n <= Real.log (n : Real) := by
    calc
      _ <= (A n) ^ 2 := haSquare
      _ <= hamiltonianAperiodicSublogDensity delta * Real.log (n : Real) := hSmall n hnB
      _ <= 1 * Real.log (n : Real) :=
        mul_le_mul_of_nonneg_right hBudget.2.2.1 hLog
      _ = _ := one_mul _
  have hExponent : hamiltonianAperiodicErrorConstant delta * (A n) ^ 2 <=
      Real.log (n : Real) / 18 := by
    calc
      _ <= hamiltonianAperiodicErrorConstant delta *
          (hamiltonianAperiodicSublogDensity delta * Real.log (n : Real)) :=
        mul_le_mul_of_nonneg_left (hSmall n hnB) hBudget.1.le
      _ = (hamiltonianAperiodicErrorConstant delta * hamiltonianAperiodicSublogDensity delta) *
          Real.log (n : Real) := by ring
      _ <= (1 / 18 : Real) * Real.log (n : Real) :=
        mul_le_mul_of_nonneg_right hBudget.2.2.2 hLog
      _ = _ := by ring
  have hRaw := hUniform n hnP (T n) (1 / (n : Real)) (A n) hq h.1 hCap
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have hDet0 : Not (Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) -
      centeredKernel (T n) (1 / (n : Real))) = 0) := ne_of_gt hRaw.2.1
  have hGram0 : Not (realGramDeterminantFactor
      (centeredKernel (T n) (1 / (n : Real))) 1 = 0) := by linarith only [hRaw.2.2.1]
  have hIdentity := hamiltonian_aperiodic_count_reference_identity (T n) (1 / (n : Real))
    (by simpa only [Fintype.card_fin] using hn1) hDet0 hGram0
  have hRelative :
      abs (hamiltonianCycleSum (T n) /
        hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) - 1) <=
          17 * (n : Real) ^ (-1 / 9 : Real) *
            Real.exp (hamiltonianAperiodicErrorConstant delta * (A n) ^ 2) := by
    rw [<- hIdentity]
    exact hRaw.2.2.2
  have hReference : 0 < hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) := by
    unfold hamiltonianAperiodicCycleReference
    rw [Fintype.card_fin]
    exact mul_pos
      (mul_pos
        (div_pos (by exact_mod_cast Nat.factorial_pos (n - 1)) (pow_pos hnPos n)) hRaw.2.1)
      (lt_of_lt_of_le (by norm_num) hRaw.2.2.1)
  refine And.intro hReference (And.intro hRelative ?_)
  calc
    _ <= 17 * (n : Real) ^ (-1 / 9 : Real) *
        Real.exp (hamiltonianAperiodicErrorConstant delta * (A n) ^ 2) := hRelative
    _ = 17 * ((n : Real) ^ (-1 / 9 : Real) *
        Real.exp (hamiltonianAperiodicErrorConstant delta * (A n) ^ 2)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left
      (hamiltonian_aperiodic_power_from_exponent (n : Real)
        (hamiltonianAperiodicErrorConstant delta) (A n) hnPos hExponent) (by norm_num)

theorem stochastic_aperiodic_family_limit
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (A : Nat -> Real) (T : (n : Nat) -> Matrix (Fin n) (Fin n) Real)
    (hFamily : HamiltonianAperiodicStochasticFamily delta A T)
    (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, 256 <= N0 /\ forall n : Nat, N0 <= n ->
      0 < hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) /\
        abs (hamiltonianCycleSum (T n) /
          hamiltonianAperiodicCycleReference (T n) (1 / (n : Real)) - 1) <= eps := by
  choose P hP hPower using stochastic_aperiodic_family_quantitative delta hDelta hDelta1 A T hFamily
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    (17 / eps) (div_pos (by norm_num) hEps) 0 (1 / 18) (by norm_num)
  let N0 := max P B
  refine Exists.intro N0 (And.intro (hP.trans (le_max_left _ _)) ?_)
  intro n hn
  have hnP : P <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := (le_max_right _ _).trans hn
  have hnPos : 0 < (n : Real) := by
    have hh := hP.trans hnP
    exact_mod_cast (show 0 < n by omega)
  have hx : 0 < (n : Real) ^ (1 / 18 : Real) := Real.rpow_pos_of_pos hnPos _
  have hBound : 17 / eps <= (n : Real) ^ (1 / 18 : Real) := by
    simpa only [pow_zero, mul_one] using hSmall n hnB
  have hCross : 17 <= eps * (n : Real) ^ (1 / 18 : Real) := by
    have h := mul_le_mul_of_nonneg_left hBound hEps.le
    have hId : eps * (17 / eps) = 17 := by field_simp
    rwa [hId] at h
  have hId : (n : Real) ^ (-1 / 18 : Real) = 1 / (n : Real) ^ (1 / 18 : Real) := by
    rw [show (-1 / 18 : Real) = -(1 / 18 : Real) by ring, Real.rpow_neg hnPos.le]
    exact (one_div _).symm
  have hRatio : 17 * (n : Real) ^ (-1 / 18 : Real) <= eps := by
    rw [hId]
    calc
      _ = 17 / (n : Real) ^ (1 / 18 : Real) := by ring
      _ <= (eps * (n : Real) ^ (1 / 18 : Real)) / (n : Real) ^ (1 / 18 : Real) :=
        div_le_div_of_nonneg_right hCross hx.le
      _ = eps := by field_simp
  have h := hPower n hnP
  exact And.intro h.1 (h.2.2.trans hRatio)

end PrimeFactorOscillations
