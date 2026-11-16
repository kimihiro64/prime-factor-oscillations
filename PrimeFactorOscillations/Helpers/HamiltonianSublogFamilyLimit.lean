/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteStirlingLimit

/-! # The full sublogarithmic family limit, with actual weighted unoriented counts -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

structure HamiltonianSublogStochasticFamily
    (rho : Real) (A : Nat -> Real)
    (T : (m : Nat) -> Matrix (Fin m) (Fin m) Real) : Prop where
  eventual_admissible : exists M0 : Nat, forall m : Nat, M0 <= m ->
    1 <= A m /\
      (forall i, Finset.univ.sum (fun j => T m i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => T m i j) = 1) /\
      (forall i j, 0 <= T m i j) /\
      (forall i j, T m i j <= A m * (1 / (m : Real))) /\
      norm (centeredKernel (T m) (1 / (m : Real))) <= rho
  sublogarithmic : forall b : Real, 0 < b -> exists M0 : Nat,
    forall m : Nat, M0 <= m -> A m <= b * Real.log (m : Real)

theorem stochastic_sublog_bipartite_family_power
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (A : Nat -> Real) (T : (m : Nat) -> Matrix (Fin m) (Fin m) Real)
    (hFamily : HamiltonianSublogStochasticFamily rho A T) :
    exists M0 : Nat, 256 <= M0 /\ forall m : Nat, M0 <= m ->
      abs (hamiltonianBipartiteCountRatio (T m) - 1) <= (m : Real) ^ (-1 / 2 : Real) /\
      abs ((hamiltonianCycleSum (bipartiteLift (T m)) / 2) /
        (Real.pi * Real.exp (-2 * (m : Real))) - 1) <=
          2 * (m : Real) ^ (-1 / 2 : Real) := by
  choose N hN hUniform using stochastic_bipartite_sublog_count_uniform.{0} rho hRho0 hRho1
  choose D hData using hFamily.eventual_admissible
  choose B hCap using hFamily.sublogarithmic (hamiltonianSublogCountDensity rho)
    (hamiltonian_sublog_density_positive rho)
  let M0 := max N (max D B)
  refine Exists.intro M0 (And.intro (hN.trans (le_max_left _ _)) ?_)
  intro m hm
  have hmN : N <= m := (le_max_left _ _).trans hm
  have hmD : D <= m := by dsimp [M0] at hm; omega
  have hmB : B <= m := by dsimp [M0] at hm; omega
  have hm256 : 256 <= m := hN.trans hmN
  have hm1 : 1 <= m := by omega
  have hmPos : 0 < (m : Real) := by exact_mod_cast (show 0 < m by omega)
  letI : NeZero m := NeZero.mk (by omega)
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    rw [Fintype.card_fin]
    field_simp [ne_of_gt hmPos]
  have h := hData m hmD
  have hRaw := hUniform (Fin m) (by simpa only [Fintype.card_fin] using hmN)
    (T m) (1 / (m : Real)) (A m) hq h.1
    (by simpa only [Fintype.card_fin] using hCap m hmB)
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have hCount : abs (hamiltonianBipartiteCountRatio (T m) - 1) <=
      (m : Real) ^ (-1 / 2 : Real) := by simpa only [Fintype.card_fin] using hRaw
  refine And.intro hCount ?_
  simpa only [Fintype.card_fin] using
    hamiltonian_bipartite_pi_error_from_factorial (T m)
      (by simpa only [Fintype.card_fin] using hm1)
      (by simpa only [Fintype.card_fin] using hCount)

theorem stochastic_sublog_bipartite_family_limit
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (A : Nat -> Real) (T : (m : Nat) -> Matrix (Fin m) (Fin m) Real)
    (hFamily : HamiltonianSublogStochasticFamily rho A T)
    (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, 256 <= M0 /\ forall m : Nat, M0 <= m ->
      abs (hamiltonianBipartiteCountRatio (T m) - 1) <= eps /\
      abs ((hamiltonianCycleSum (bipartiteLift (T m)) / 2) /
        (Real.pi * Real.exp (-2 * (m : Real))) - 1) <= eps := by
  choose A0 hA0 hPower using
    stochastic_sublog_bipartite_family_power rho hRho0 hRho1 A T hFamily
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    (2 / eps) (div_pos (by norm_num) hEps) 0 (1 / 2) (by norm_num)
  let M0 := max A0 B
  refine Exists.intro M0 (And.intro (hA0.trans (le_max_left _ _)) ?_)
  intro m hm
  have hmA : A0 <= m := (le_max_left _ _).trans hm
  have hmB : B <= m := (le_max_right _ _).trans hm
  have hmPos : 0 < (m : Real) := by
    have hh := hA0.trans hmA
    exact_mod_cast (show 0 < m by omega)
  have hx : 0 < (m : Real) ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hmPos _
  have hBound : 2 / eps <= (m : Real) ^ (1 / 2 : Real) := by
    simpa only [pow_zero, mul_one] using hSmall m hmB
  have hCross : 2 <= eps * (m : Real) ^ (1 / 2 : Real) := by
    have h := mul_le_mul_of_nonneg_left hBound hEps.le
    have hId : eps * (2 / eps) = 2 := by field_simp [ne_of_gt hEps]
    rwa [hId] at h
  have hId : (m : Real) ^ (-1 / 2 : Real) = 1 / (m : Real) ^ (1 / 2 : Real) := by
    rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by ring, Real.rpow_neg hmPos.le]
    exact (one_div _).symm
  have hRatio : 2 * (m : Real) ^ (-1 / 2 : Real) <= eps := by
    rw [hId]
    calc
      _ = 2 / (m : Real) ^ (1 / 2 : Real) := by ring
      _ <= (eps * (m : Real) ^ (1 / 2 : Real)) /
          (m : Real) ^ (1 / 2 : Real) :=
        div_le_div_of_nonneg_right hCross hx.le
      _ = eps := by field_simp [ne_of_gt hx]
  have hPower0 : 0 <= (m : Real) ^ (-1 / 2 : Real) := Real.rpow_nonneg hmPos.le _
  have h := hPower m hmA
  exact And.intro (h.1.trans (by linarith only [hRatio, hPower0])) (h.2.trans hRatio)

end PrimeFactorOscillations
