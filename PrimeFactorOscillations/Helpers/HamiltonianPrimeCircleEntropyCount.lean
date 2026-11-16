/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleOrientation

/-! # The actual unoriented prime-circle count at its exact entropy -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeCycleRelation (m : Nat) :
    Sum (Fin m) (Fin m) -> Sum (Fin m) (Fin m) -> Prop
  | Sum.inl i, Sum.inr j => Nat.Prime (2 * i.val + 2 * j.val + 3)
  | Sum.inr j, Sum.inl i => Nat.Prime (2 * i.val + 2 * j.val + 3)
  | _, _ => False

instance hamiltonianPrimeCycleRelationDecidable (m : Nat) :
    DecidableRel (hamiltonianPrimeCycleRelation m) := by
  intro i j
  cases i <;> cases j <;> dsimp only [hamiltonianPrimeCycleRelation] <;> infer_instance

def hamiltonianPrimeCircleCount (m : Nat) : Nat :=
  (hamiltonianUnorientedCycles (hamiltonianPrimeCycleRelation m)).card

def hamiltonianPrimeFeasible (m : Nat) (X : Matrix (Fin m) (Fin m) Real) : Prop :=
  (forall i j, 0 <= X i j) /\
  (forall i, Finset.univ.sum (fun j => X i j) = 1) /\
  (forall j, Finset.univ.sum (fun i => X i j) = 1) /\
  (forall i j, Not (Nat.Prime (2 * i.val + 2 * j.val + 3)) -> X i j = 0)

def hamiltonianPrimeEntropyMaximum (m : Nat) (H : Real) : Prop :=
  (exists X : Matrix (Fin m) (Fin m) Real,
    And (hamiltonianPrimeFeasible m X) (hamiltonianCrossEntropy X = H)) /\
  forall X : Matrix (Fin m) (Fin m) Real,
    hamiltonianPrimeFeasible m X -> hamiltonianCrossEntropy X <= H

def hamiltonianPrimeCircleRatio (m : Nat) (H : Real) : Real :=
  ((m : Real) ^ m / (m.factorial : Real)) ^ 2 * (2 * (m : Real)) *
    Real.exp (-2 * H) * (hamiltonianPrimeCircleCount m : Real)

theorem hamiltonian_prime_cycle_relation_symmetric (m : Nat)
    (i j : Sum (Fin m) (Fin m)) :
    hamiltonianPrimeCycleRelation m i j -> hamiltonianPrimeCycleRelation m j i := by
  cases i <;> cases j <;> exact fun h => h

theorem hamiltonian_prime_adjacency_indicator (m : Nat) :
    bipartiteLift (hamiltonianPrimeCrossAdjacency m) =
      (fun i j => if hamiltonianPrimeCycleRelation m i j then (1 : Real) else 0) := by
  ext i j
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      hamiltonianPrimeCrossAdjacency, hamiltonianPrimeCycleRelation]

theorem hamiltonian_prime_cycle_sum_count (m : Nat) (hm : 2 <= m) :
    hamiltonianCycleSum (bipartiteLift (hamiltonianPrimeCrossAdjacency m)) =
      2 * (hamiltonianPrimeCircleCount m : Real) := by
  rw [hamiltonian_prime_adjacency_indicator, hamiltonian_indicator_cycle_count]
  have hCard : 3 <= Fintype.card (Sum (Fin m) (Fin m)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have h := hamiltonian_unoriented_cycle_card (hamiltonianPrimeCycleRelation m)
    (hamiltonian_prime_cycle_relation_symmetric m) hCard
  exact_mod_cast h

theorem hamiltonian_prime_entropy_maximum_unique (m : Nat) (H K : Real)
    (hH : hamiltonianPrimeEntropyMaximum m H) (hK : hamiltonianPrimeEntropyMaximum m K) :
    H = K := by
  choose X hX hHX using hH.1
  choose Y hY hKY using hK.1
  have h1 := hH.2 Y hY
  have h2 := hK.2 X hX
  rw [hHX] at h2
  rw [hKY] at h1
  exact le_antisymm h2 h1

theorem hamiltonian_prime_scaling_attains_entropy (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (hNonneg : forall i j, 0 <= hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) :
    hamiltonianPrimeEntropyMaximum m
      (hamiltonianCrossEntropy (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) := by
  have hSupport (i j : Fin m) (hp : Not (Nat.Prime (2 * i.val + 2 * j.val + 3))) :
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0 := by
    simp only [hamiltonianScaledCross, hamiltonian_prime_cross_formula, hp,
      ite_false, mul_zero, zero_mul]
  constructor
  . exact Exists.intro _ (And.intro (And.intro hNonneg (And.intro hRows
      (And.intro hCols hSupport))) rfl)
  . intro X hX
    exact hamiltonian_prime_entropy_maximum m hm z hPos hRows hCols X
      hX.1 hX.2.1 hX.2.2.1 hX.2.2.2

theorem hamiltonian_prime_weighted_ratio_entropy (m : Nat) (hm : 2 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) :
    hamiltonianBipartiteCountRatio (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) =
      hamiltonianPrimeCircleRatio m
        (hamiltonianCrossEntropy (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) := by
  unfold hamiltonianBipartiteCountRatio hamiltonianPrimeCircleRatio
  rw [hamiltonian_prime_cycle_entropy_weight m (by omega) z hPos hRows hCols,
    hamiltonian_prime_cycle_sum_count m hm]
  simp only [Fintype.card_fin]
  ring

theorem hamiltonian_prime_circle_entropy_relative_uniform :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        And (exists H : Real, hamiltonianPrimeEntropyMaximum m H)
          (forall H : Real, hamiltonianPrimeEntropyMaximum m H ->
            abs (hamiltonianPrimeCircleRatio m H - 1) <=
              (m : Real) ^ (-3 / 5 : Real))) := by
  choose M0 hM0 hCount using hamiltonian_actual_prime_relative_count 1 (by norm_num)
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm
  have hm2 : 2 <= m := by omega
  choose z hZ hPos hNonneg hRows hCols hSupport hCap hGap hError using hCount m hm
  let H0 := hamiltonianCrossEntropy
    (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
  have hMaximum : hamiltonianPrimeEntropyMaximum m H0 :=
    hamiltonian_prime_scaling_attains_entropy m (by omega) z hPos hNonneg hRows hCols
  refine And.intro (Exists.intro H0 hMaximum) ?_
  intro H hH
  have hEq := hamiltonian_prime_entropy_maximum_unique m H H0 hH hMaximum
  subst H
  have hRatio := hamiltonian_prime_weighted_ratio_entropy m hm2 z hPos hRows hCols
  rwa [hRatio] at hError

end PrimeFactorOscillations.LPF
