/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicFamilyLimit
import PrimeFactorOscillations.Helpers.HamiltonianGraphEntropyGauge
import PrimeFactorOscillations.Helpers.HamiltonianSublogFamilyLimit

/-! # Both graph-entropy asymptotics for actual reversal classes

The same graph and positive vertex weights are used in the stochastic
family hypothesis and the final actual graph count. Zero support is
allowed. The two original density domains remain distinct.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_aperiodic_graph_entropy_family_limit
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (R : (n : Nat) -> Fin n -> Fin n -> Prop)
    [forall n, DecidableRel (R n)]
    (u : (n : Nat) -> Fin n -> Real) (A : Nat -> Real)
    (hSym : forall n (i j : Fin n), R n i j -> R n j i)
    (hPos : forall n (i : Fin n), 0 < u n i)
    (hFamily : HamiltonianAperiodicStochasticFamily delta A
      (fun n => hamiltonianGraphScaledKernel (R n) (u n)))
    (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, 256 <= N0 /\ forall n : Nat, N0 <= n ->
      0 < hamiltonianGraphEntropyReference (R n) (u n) (1 / (n : Real)) /\
        abs ((hamiltonianGraphUnorientedCount (R n) : Real) /
          hamiltonianGraphEntropyReference (R n) (u n) (1 / (n : Real)) - 1) <= eps := by
  choose P hP hCount using stochastic_aperiodic_family_limit delta hDelta hDelta1 A
    (fun n => hamiltonianGraphScaledKernel (R n) (u n)) hFamily eps hEps
  choose D hData using hFamily.eventual_admissible
  let N0 := max P D
  refine Exists.intro N0 (And.intro (hP.trans (le_max_left _ _)) ?_)
  intro n hn
  have hnP : P <= n := (le_max_left _ _).trans hn
  have hnD : D <= n := (le_max_right _ _).trans hn
  have hn256 : 256 <= n := hP.trans hnP
  have hCard : 3 <= Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  have hRho : 1 - delta < 1 := by linarith only [hDelta]
  have h := hData n hnD
  have hRaw := hCount n hnP
  have hRef := hamiltonian_graph_entropy_reference_identity (R n) (u n) (1 / (n : Real))
    (1 - delta) (hSym n) hCard hRho h.2.2.2.2.2
  have hPositive : 0 < hamiltonianGraphEntropyReference (R n) (u n) (1 / (n : Real)) := by
    rw [hRef]
    exact mul_pos (div_pos hRaw.1 (by norm_num)) (Real.exp_pos _)
  refine And.intro hPositive ?_
  rw [hamiltonian_graph_aperiodic_entropy_ratio (R n) (u n) (1 / (n : Real))
    (1 - delta) (hSym n) hCard (hPos n) hRho h.2.2.2.2.2 (ne_of_gt hRaw.1)]
  exact hRaw.2

theorem hamiltonian_bipartite_graph_entropy_family_limit
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (R : (m : Nat) -> Sum (Fin m) (Fin m) -> Sum (Fin m) (Fin m) -> Prop)
    [forall m, DecidableRel (R m)]
    (u : (m : Nat) -> Sum (Fin m) (Fin m) -> Real)
    (A : Nat -> Real) (T : (m : Nat) -> Matrix (Fin m) (Fin m) Real)
    (hSym : forall m (i j : Sum (Fin m) (Fin m)), R m i j -> R m j i)
    (hPos : forall m (i : Sum (Fin m) (Fin m)), 0 < u m i)
    (hBlock : forall m, hamiltonianGraphScaledKernel (R m) (u m) = bipartiteLift (T m))
    (hFamily : HamiltonianSublogStochasticFamily rho A T)
    (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, 256 <= M0 /\ forall m : Nat, M0 <= m ->
      0 < Real.pi * Real.exp (-2 * (m : Real) - 2 * hamiltonianGraphLogGauge (u m)) /\
        abs ((hamiltonianGraphUnorientedCount (R m) : Real) /
          (Real.pi * Real.exp (-2 * (m : Real) - 2 * hamiltonianGraphLogGauge (u m))) - 1) <= eps := by
  choose M0 hM0 hCount using stochastic_sublog_bipartite_family_limit rho hRho0 hRho1 A T hFamily eps hEps
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm
  have hm2 : 2 <= m := by omega
  refine And.intro (mul_pos Real.pi_pos (Real.exp_pos _)) ?_
  rw [hamiltonian_graph_bipartite_pi_ratio (R m) (u m) (T m) hm2 (hSym m) (hPos m) (hBlock m)]
  exact (hCount m hm).2

end PrimeFactorOscillations
